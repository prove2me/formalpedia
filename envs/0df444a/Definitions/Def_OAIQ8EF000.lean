-- Prove2me | Definitions.Def_OAIQ8EF000
-- name    : OAIQ8EF000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:01:54.50509+00:00
-- url     : https://prove2.me/theorems/eac2d693-26e3-4f4e-8995-0c18b32bf188
-- title:
--   Definitions bundle OAIQ8EF000 of the split of OpenAI, Short Egyptian fractions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.egyptian_length_is_minimum`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.missing_denominator_semantics`, `OAI.Problem337.one_expansions_finite_and_bounded`, `OAI.Problem337.prescribed_denominator_corollary` and `OAI.Problem337.quantitative_marked_length`, carved from OpenAI's openai/math development (OpenAI, *Short Egyptian fractions*, OpenAI Math Release, September 25, 2026, result family 25, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 203 declarations of OpenAI's Lean: 133 definitions, 7 inductive types or structures, 5 instances and 58 theorems. The definitions and types are `OAI.Problem337.CompositeSpectral.remainderCollisionCount`, `OAI.Problem337.CompositeSpectral.sumTuples`, `OAI.Problem337.CompositeSupply.BadModulus`, `OAI.Problem337.CompositeSupply.badMultiples`, `OAI.Problem337.CompositeSupply.base`, `OAI.Problem337.CompositeSupply.instDecidablePredNatBadModulus`, `OAI.Problem337.CompositeSupply.instDecidablePredNatBadModulus_1`, `OAI.Problem337.CompositeSupply.multiplier`, `OAI.Problem337.CompositeSupply.primeCount`, `OAI.Problem337.CountingPadding.pad`, `OAI.Problem337.CubeFreeDensity.bad`, `OAI.Problem337.CubeFreeDensity.good`, `OAI.Problem337.CyclicSmoothing.normalizedKernel`, `OAI.Problem337.CyclicSmoothing.window`, `OAI.Problem337.DenseEgyptianFamily`, `OAI.Problem337.DensityBadFamily`, `OAI.Problem337.DensityResidueFamily`, `OAI.Problem337.DensityResidueFamily.GoodSets`, `OAI.Problem337.DensityResidueFamily.toBadFamily`, `OAI.Problem337.Descent.UnitListAtMost`, `OAI.Problem337.DivisorClasses.BandClass`, `OAI.Problem337.DivisorClasses.LargeClass`, `OAI.Problem337.DivisorClasses.PrefixWitness`, `OAI.Problem337.DivisorClasses.SmallClass`, `OAI.Problem337.DivisorDense`, `OAI.Problem337.DivisorMoment.IntermediatePrefixWitness`, `OAI.Problem337.DivisorMoment.divisorMomentWeight`, `OAI.Problem337.DivisorMomentAbsorption.harmonicCoefficient`, `OAI.Problem337.DivisorMomentAbsorption.largeCoefficient`, `OAI.Problem337.DyadicBands.InBand`, `OAI.Problem337.DyadicBands.bandCount`, `OAI.Problem337.ExponentialSum.phase`, `OAI.Problem337.ExponentialSum.phaseWeight`, `OAI.Problem337.GeometricDensity.NormalizedResidueData`, `OAI.Problem337.GeometricDensity.NormalizedResidueData.toResidueData`, `OAI.Problem337.GeometricDensity.ResidueData`, `OAI.Problem337.GeometricDensity.ResidueData.toFamily`, `OAI.Problem337.GeometricDensity.contraction`, `OAI.Problem337.GeometricDensity.cutoff`, `OAI.Problem337.GeometricDensity.depth` and 100 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `EgyptianFractions_BackwardExpansions`, `EgyptianFractions_BilinearFourier`, `EgyptianFractions_BinaryExpansion`, `EgyptianFractions_CeilResidue`, `EgyptianFractions_CollisionCounting`, `EgyptianFractions_CompositeBadDensity`, `EgyptianFractions_CompositeBadDensityBound`, `EgyptianFractions_CompositeBadModuli`, `EgyptianFractions_CompositeSpectral`, `EgyptianFractions_CompositeSupplySize`, `EgyptianFractions_CorrelationPhase`, `EgyptianFractions_CountingPadding`, `EgyptianFractions_CubeFreeDensity`, `EgyptianFractions_CubeFreeSupplyFromExceptions`, `EgyptianFractions_CyclicKernel`, `EgyptianFractions_CyclicSmoothing`, `EgyptianFractions_DensityAssembly`, `EgyptianFractions_DensityMomentBridge`, `EgyptianFractions_DiscreteFirstDerivative`, `EgyptianFractions_DivisorClasses`, `EgyptianFractions_DivisorDensity`, `EgyptianFractions_DivisorEnergyNesting`, `EgyptianFractions_DivisorFactorBound`, `EgyptianFractions_DivisorMomentAbsorption`, `EgyptianFractions_DivisorPointwiseUniform`, `EgyptianFractions_DivisorSplit`, `EgyptianFractions_DyadicBands`, `EgyptianFractions_EightProductConductor`, `EgyptianFractions_ExactPadding`, `EgyptianFractions_FejerBounds`, `EgyptianFractions_FiniteEulerBound`, `EgyptianFractions_FiniteResidueIndices`, `EgyptianFractions_FixedSumFinite`, `EgyptianFractions_ForwardDifference`, `EgyptianFractions_GeometricRandomRanges`, `EgyptianFractions_GeometricRawDensity`, `EgyptianFractions_GoodNumeratorSets`, `EgyptianFractions_GreedyPreparation`, `EgyptianFractions_HighResidueDistribution`, `EgyptianFractions_HitCount`, `EgyptianFractions_IntermediatePrefixClass`, `EgyptianFractions_IteratedDifferencing`, `EgyptianFractions_LargePrefixClass`, `EgyptianFractions_MainUpperReduction`, `EgyptianFractions_MarkedGreedy`, `EgyptianFractions_MarkedGrouping`, `EgyptianFractions_MarkedGroupingUnits`, `EgyptianFractions_MarkedReduction`, `EgyptianFractions_MarkerOccurrence`, `EgyptianFractions_MonotoneBlocks`, `EgyptianFractions_OddPrimorial`, `EgyptianFractions_PhaseExtension`, `EgyptianFractions_PrimePool`, `EgyptianFractions_PrimeProductBound`, `EgyptianFractions_PrimeProductFibers`, `EgyptianFractions_RandomCommonRealization`, `EgyptianFractions_RandomExposure`, `EgyptianFractions_RandomProductParameters`, `EgyptianFractions_RandomResidueRealization`, `EgyptianFractions_RandomSecondMoment`, `EgyptianFractions_RationalDivisorSupplyAlgebra`, `EgyptianFractions_RawDensityParameters`, `EgyptianFractions_RawDensityUpper`, `EgyptianFractions_ReciprocalPhaseUniform`, `EgyptianFractions_ReducedCharacter`, `EgyptianFractions_ReducedCollisionFourier`, `EgyptianFractions_ResidueDenominator`, `EgyptianFractions_ResidueLevels`, `EgyptianFractions_ResidueRegimeSplice`, `EgyptianFractions_ResidueStep`, `EgyptianFractions_RoughModulusBlocks`, `EgyptianFractions_RoughPart`, `EgyptianFractions_SampledResidueDenominator`, `EgyptianFractions_SmoothRankin`, `EgyptianFractions_SparseBadDivisorTail`, `EgyptianFractions_SupplySize`, `EgyptianFractions_TerminalAssembly`, `EgyptianFractions_TerminalBridge`, `EgyptianFractions_TerminalDepth`, `EgyptianFractions_TerminalFiniteBudget`, `EgyptianFractions_TerminalRecursion`, `EgyptianFractions_ThinSupplyBase`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget`, `OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues`, `OAI.Problem337.deterministic_mean_two_errors`, `OAI.Problem337.eventually_residue_level_moment` and `OAI.Problem337.main_upper_of_raw_density_supply`; the proofs of `OAI.Problem337.DivisorMoment.eventually_intermediate_band_budget`, `OAI.Problem337.RandomProducts.eventually_common_geometric_random_fractional_residues`, `OAI.Problem337.counting_double_log_order`, `OAI.Problem337.deterministic_mean_two_errors`, `OAI.Problem337.eventually_residue_level_moment`, `OAI.Problem337.every_exact_marker_occurs`, `OAI.Problem337.exact_marker_padding`, `OAI.Problem337.main_double_log_order`, `OAI.Problem337.main_upper_of_raw_density_supply` and `OAI.Problem337.quantitative_marked_length`.
-- source:
--   OpenAI, Short Egyptian fractions, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 25; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Short-Egyptian-fractions-September-25-2026/Short-Egyptian-fractions-September-25-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ8_EF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The division step underlying both the terminal and backward numerator descent. -/
theorem residue_step_identity (M Q u t z h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (ht : 0 < t) (hz : 0 < z)
    (htM : t ∣ M) (hres : Q * t + h = u * z) :
    (u : ℚ) / (M * Q : ℕ) =
      (1 : ℚ) / ((M / t) * z : ℕ) +
        (1 : ℚ) / z * ((h : ℚ) / (M * Q : ℕ)) := by
  have hMt : M / t * t = M := Nat.div_mul_cancel htM
  have hMtpos : 0 < M / t := by nlinarith
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have htq : (0 : ℚ) < t := by exact_mod_cast ht
  have hzq : (0 : ℚ) < z := by exact_mod_cast hz
  have hMtq : (0 : ℚ) < (M / t : ℕ) := by exact_mod_cast hMtpos
  have heq : ((M / t : ℕ) : ℚ) * t = M := by exact_mod_cast hMt
  have hresq : (Q : ℚ) * t + h = (u : ℚ) * z := by exact_mod_cast hres
  push_cast
  field_simp
  nlinarith

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BackwardExpansions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.Descent

/-- Length-bounded positive unit-fraction lists; repetitions are allowed at
this stage of the density construction. -/
def UnitListAtMost (x : ℚ) (B : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ B ∧ ∃ n : Fin k → ℕ,
    (∀ i, 0 < n i) ∧ (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x

end Problem337.Descent

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BilinearFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The positive-sign discrete Fourier transform, convenient for residue products. -/
def residueFourier {q : ℕ} [NeZero q] (β : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑ y, β y * ZMod.stdAddChar (x * y)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BinaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Binary digits give a short expansion whenever a large power of two
is available as a divisor of the denominator. -/
theorem binary_unit_fraction_list (u M a : ℕ) (huM : u < M)
    (hu : u < 2 ^ (a + 1)) (hdiv : 2 ^ a ∣ M) :
    ∃ l : List ℕ, (∀ d ∈ l, 2 ≤ d) ∧ l.length ≤ a + 1 ∧
      (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = (u : ℚ) / M := by
  let l := u.bitIndices.map (fun i => M / 2 ^ i)
  have hi : ∀ i ∈ u.bitIndices, i ≤ a := by
    intro i hi
    have hp := (Nat.two_pow_le_of_mem_bitIndices hi).trans_lt hu
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hp
    omega
  have hd : ∀ i ∈ u.bitIndices, 2 ^ i ∣ M := by
    intro i h
    exact (Nat.pow_dvd_pow 2 (hi i h)).trans hdiv
  have hM : (M : ℚ) ≠ 0 := by
    exact_mod_cast (show M ≠ 0 by omega)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro d hdmem
    obtain ⟨i, himem, rfl⟩ := List.mem_map.mp hdmem
    have hpow : 2 ^ i ≤ u := Nat.two_pow_le_of_mem_bitIndices himem
    have hp : 0 < 2 ^ i := by positivity
    have hm : 2 ^ i < M := hpow.trans_lt huM
    have hmul := Nat.mul_div_cancel' (hd i himem)
    by_contra hlt
    have hle : M / 2 ^ i ≤ 1 := by omega
    have := Nat.mul_le_mul_left (2 ^ i) hle
    omega
  · change (u.bitIndices.map _).length ≤ _
    rw [List.length_map, ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
    calc
      u.bitIndices.toFinset.card ≤ (Finset.range (a + 1)).card := by
        apply Finset.card_le_card
        intro i himem
        have := hi i (List.mem_toFinset.mp himem)
        simpa using this
      _ = a + 1 := Finset.card_range _
  · change ((u.bitIndices.map (fun i => M / 2 ^ i)).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = _
    simp only [List.map_map, Function.comp_def]
    have heq : u.bitIndices.map (fun i => (1 : ℚ) / (M / 2 ^ i : ℕ)) =
        u.bitIndices.map (fun i => (2 : ℚ) ^ i * (M : ℚ)⁻¹) := by
      apply List.map_congr_left
      intro i himem
      have hp : ((2 ^ i : ℕ) : ℚ) ≠ 0 := by positivity
      rw [Nat.cast_div (hd i himem) hp, one_div_div]
      simp [div_eq_mul_inv]
    rw [heq, List.sum_map_mul_right]
    have hsum : (u.bitIndices.map (fun i => (2 : ℚ) ^ i)).sum = (u : ℚ) := by
      have h := congrArg (fun n : ℕ => (n : ℚ)) (Nat.sum_map_two_pow_bitIndices u)
      simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_pow, Nat.cast_ofNat] using h
    rw [hsum, div_eq_mul_inv]

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CeilResidue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The same remainder normalized by its modulus is the real fractional part. -/
theorem residue_div_eq_fract_neg {u N z h : ℕ} (hh : h < u)
    (heq : u * z = N + h) :
    (h : ℝ) / u = Int.fract (-(N : ℝ) / u) := by
  have hu : (0 : ℝ) < (u : ℝ) := by exact_mod_cast (show 0 < u by omega)
  apply Eq.symm
  apply Int.fract_eq_iff.mpr
  refine ⟨by positivity, (div_lt_one hu).mpr (by exact_mod_cast hh), -(z : ℤ), ?_⟩
  have heqR : (u : ℝ) * z = N + h := by exact_mod_cast heq
  push_cast
  rw [← sub_div]
  apply (div_eq_iff (ne_of_gt hu)).2
  nlinarith

/-- Arithmetic specifications of the nonnegative ceiling remainder. -/
theorem natural_ceil_residue_spec (u N : ℕ) (hu : 0 < u) :
    N ≤ u * ⌈(N : ℝ) / u⌉₊ ∧
    u * ⌈(N : ℝ) / u⌉₊ = N + (u * ⌈(N : ℝ) / u⌉₊ - N) ∧
    u * ⌈(N : ℝ) / u⌉₊ - N < u := by
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hlo : (N : ℝ) / u ≤ (⌈(N : ℝ) / u⌉₊ : ℝ) := Nat.le_ceil _
  have hhi : (⌈(N : ℝ) / u⌉₊ : ℝ) < (N : ℝ) / u + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hN : N ≤ u * ⌈(N : ℝ) / u⌉₊ := by
    have h := (div_le_iff₀ huR).mp hlo
    exact_mod_cast (show (N : ℝ) ≤ (u : ℝ) * (⌈(N : ℝ) / u⌉₊ : ℝ) by nlinarith)
  have hNu : u * ⌈(N : ℝ) / u⌉₊ < N + u := by
    have hmul := mul_lt_mul_of_pos_right hhi huR
    have hcancel : (N : ℝ) / u * u = N := div_mul_cancel₀ _ (ne_of_gt huR)
    exact_mod_cast (show (u : ℝ) * (⌈(N : ℝ) / u⌉₊ : ℝ) < (N : ℝ) + u by nlinarith)
  exact ⟨hN, by omega, by omega⟩

theorem natural_ceil_residue_div_eq_fract_neg (u N : ℕ) (hu : 0 < u) :
    ((u * ⌈(N : ℝ) / u⌉₊ - N : ℕ) : ℝ) / u = Int.fract (-(N : ℝ) / u) := by
  obtain ⟨_, heq, hlt⟩ := natural_ceil_residue_spec u N hu
  exact residue_div_eq_fract_neg hlt heq


end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CollisionCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Ordered pairs with equal images, including the diagonal. -/
def collisionPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) : Finset (α × α) :=
  (A ×ˢ A).filter (fun p => f p.1 = f p.2)

/-- Ordered collisions between distinct inputs. -/
def strictCollisionPairs {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) : Finset (α × α) :=
  (collisionPairs A f).filter (fun p => p.1 ≠ p.2)

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeProductBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Real

namespace Problem337

/-- Product of the first `n` primes, indexed from zero. -/
def primePrefixProduct (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SupplySize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter Real

namespace Problem337

/-- Number of primes used by a logarithmic supply construction. -/
def supplyPrimeCount (a : ℝ) (m : ℕ) : ℕ := ⌈a * Real.log (m : ℝ)⌉₊

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeSupplySize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
# Size of the fourth-power supply for cube-free moduli

The fourth-power auxiliary integer has a controlled logarithmic size.
-/
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.CompositeSupply

/-- The global divisor pool uses twice the binary logarithm of its range. -/
def primeCount (u : ℕ) : ℕ := ⌈2 * Real.log (u : ℝ) / Real.log 2⌉₊

/-- The product of the first `primeCount u` primes. -/
def base (u : ℕ) : ℕ := primePrefixProduct (primeCount u)

/-- Two powers allow the bilinear products and two powers allow stripping
all small-prime factors of a cube-free modulus. -/
def multiplier (m : ℕ) : ℕ := base (m ^ 4) ^ 4

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorEnergyNesting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Pointwise

namespace Problem337

/-- Multiplication bijects the divisor lists of two coprime integers with
the divisor list of their product. -/
def coprimeDivisorProductEquiv {P R : ℕ} (hPR : P.Coprime R) :
    (↥P.divisors × ↥R.divisors) ≃ ↥(P * R).divisors := by
  classical
  let f : (↥P.divisors × ↥R.divisors) → ↥(P * R).divisors := fun z =>
    ⟨z.1.val * z.2.val, Nat.mem_divisors.mpr
      ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors z.1.property)
        (Nat.dvd_of_mem_divisors z.2.property),
        mul_ne_zero (Nat.ne_zero_of_mem_divisors z.1.property)
          (Nat.ne_zero_of_mem_divisors z.2.property)⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b hab
    have hval := congrArg Subtype.val hab
    have hpair : (a.1.val, a.2.val) = (b.1.val, b.2.val) :=
      hPR.mul_injOn_divisors
        (Finset.mem_product.mpr ⟨a.1.property, a.2.property⟩)
        (Finset.mem_product.mpr ⟨b.1.property, b.2.property⟩) hval
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
      (Subtype.ext (congrArg Prod.snd hpair))
  · intro d
    have hd := d.property
    simp only [Nat.divisors_mul, Finset.mem_mul] at hd
    obtain ⟨a, ha, b, hb, hab⟩ := hd
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

@[simp] theorem coprimeDivisorProductEquiv_val {P R : ℕ} (hPR : P.Coprime R)
    (z : ↥P.divisors × ↥R.divisors) :
    (coprimeDivisorProductEquiv hPR z).val = z.1.val * z.2.val := rfl

/-- The normalized residue-fiber energy of the complete positive divisor list. -/
def divisorResidueEnergy (P q : ℕ) [NeZero q] : ℝ :=
  ∑ x : ZMod q,
    (((Finset.univ.filter (fun d : ↥P.divisors => (d.val : ZMod q) = x)).card : ℝ) /
      (Fintype.card ↥P.divisors : ℝ)) ^ 2

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimeProductFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- The probability mass of one residue for independent uniform prime samples. -/
def primeProductModMass (P : Finset ℕ) (s q : ℕ) (r : ZMod q) : ℝ :=
  ((Finset.univ.filter (fun a : Fin s → ↥P =>
    ((∏ i, (a i : ℕ)) : ZMod q) = r)).card : ℝ) / (P.card : ℝ)^s

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReducedCharacter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- After cancelling the gcd, the numerator is an invertible residue class. -/
def reducedFrequency (a u : ℕ) (hu : 0 < u) : (ZMod (u / a.gcd u))ˣ :=
  ZMod.unitOfCoprime (a / a.gcd u)
    (Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hu))

@[simp] lemma reducedFrequency_coe (a u : ℕ) (hu : 0 < u) :
    (reducedFrequency a u hu : ZMod (u / a.gcd u)) = (a / a.gcd u : ℕ) :=
  ZMod.coe_unitOfCoprime _ _

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReducedCollisionFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The number of ordered pairs in an indexed list with the same residue.
The indices, rather than the image set, retain all multiplicities. -/
def indexedResidueCollisionCount {ι : Type*} [Fintype ι]
    {q : ℕ} [NeZero q] (f : ι → ZMod q) : ℕ :=
  (Finset.univ.filter (fun ij : ι × ι => f ij.1 = f ij.2)).card

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeBadModuli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

namespace CompositeSupply

/-- A global, total predicate independent of any later ambient supply range.
The strict energy inequality is encoded without division or typeclass data. -/
def BadModulus (d : ℕ) : Prop :=
  2 ≤ d ∧ (base d).Coprime d ∧
    ((base d).divisors.card : ℝ)^2 <
      (d : ℝ)^(7 / 8 : ℝ) *
        ((collisionPairs (base d).divisors (fun a => a % d)).card : ℝ)

end CompositeSupply
end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SparseBadDivisorTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.SparseBadDivisorTail


/-- Positive integers up to `Y` divisible by at least one member of `A`. -/
def divisorMultiples (A : Finset ℕ) (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Y).filter (fun n => ∃ d ∈ A, d ∣ n)

/-- A finite piece of a global exceptional-modulus predicate above `2^J`. -/
def badTail (B : ℕ → Prop) [DecidablePred B] (J Y : ℕ) : Finset ℕ :=
  (Finset.Icc (2 ^ J) Y).filter B

end Problem337.SparseBadDivisorTail

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeBadDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped BigOperators

namespace Problem337.CompositeSupply
local instance instDecidablePredNatBadModulus : DecidablePred BadModulus := Classical.decPred _

/-- Integers containing a global bad conductor above the logarithmic cutoff.
This finite set depends only on the ambient range, not on any chosen modulus. -/
def badMultiples (Y : ℕ) : Finset ℕ := by
  classical
  exact SparseBadDivisorTail.divisorMultiples
    ((Finset.Icc ⌊Real.log (Y : ℝ)⌋₊ Y).filter BadModulus) Y

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorFactorBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Number of positive divisors at most a real cutoff. -/
def truncatedDivisorCount (X : ℝ) (n : ℕ) : ℕ :=
  (n.divisors.filter (fun a : ℕ => (a : ℝ) ≤ X)).card

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RoughPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The part of an integer supported on primes at least `R`, retaining their
full multiplicities. The definition at zero is harmlessly the empty product. -/
def roughPart (R : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter (fun p : ℕ => R ≤ (p : ℝ))).prod

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ThinSupplyBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- Prime-prefix supply with an arbitrary logarithmic coefficient. -/
def thinSupplyBase (a : ℝ) (u : ℕ) : ℕ :=
  primePrefixProduct (supplyPrimeCount a u)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RoughModulusBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- Bad moduli on one block use one common divisor list.  This deliberate
fixed-base choice is needed for the off-diagonal double count. -/
def roughModulusBadBlock (D : ℕ) : Finset ℕ := by
  classical
  let A := (thinSupplyBase (2 / Real.log 2) D).divisors
  exact (Finset.Ico D (2 * D)).filter (fun q =>
    (∀ p ∈ q.primeFactorsList, Real.log (2 * (D : ℝ)) ≤ (p : ℝ)) ∧
    (A.card : ℝ) ^ 2 ≤ (q : ℝ) ^ (7 / 8 : ℝ) *
      ((collisionPairs A (fun a => a % q)).card : ℝ))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeBadDensityBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply
local instance instDecidablePredNatBadModulus_1 : DecidablePred BadModulus := Classical.decPred _

end Problem337.CompositeSupply

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CompositeSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- Ordered tuples with a prescribed sum in a finite cyclic group. -/
def sumTuples {q : ℕ} [NeZero q] {X : Type*} [Fintype X]
    (f : X → ZMod q) (k : ℕ) (t : ZMod q) : Finset (Fin k → X) := by
  classical
  exact Finset.univ.filter (fun v => ∑ i, f (v i) = t)

end Problem337.CompositeSpectral

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ForwardDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Set
open scoped ContDiff Topology

namespace Problem337

/-- Iterated forward differences, with the shifts in list order. -/
def forwardDifference : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => fun x => forwardDifference hs f (x + h) - forwardDifference hs f x

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IteratedDifferencing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

/-- A single multiplicative difference of a complex sequence. -/
def correlationShift (a : ℤ → ℂ) (h : ℤ) : ℤ → ℂ :=
  fun n => a (n + h) * conj (a n)

/-- Successive multiplicative differences, in their order of application. -/
def iteratedCorrelation (a : ℤ → ℂ) : List ℤ → ℤ → ℂ
  | [] => a
  | h :: hs => iteratedCorrelation (correlationShift a h) hs

/-- The elementary square-root budget obtained from repeated differencing. -/
def differencingBudget (H : ℕ) : ℕ → ℝ → ℝ
  | 0, B => B
  | r + 1, B => Real.sqrt (2 / (H : ℝ) + 2 * differencingBudget H r B)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CorrelationPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

/-- The unit complex phase with frequency one. -/
def differencingPhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem differencingPhase_norm (x : ℝ) : ‖differencingPhase x‖ = 1 := by
  simp [differencingPhase, Complex.norm_exp]

/-- A phase sequence with zero extension outside a closed integer interval. -/
def intervalPhase (f : ℝ → ℝ) (L U : ℤ) : ℤ → ℂ :=
  fun n => if L ≤ n ∧ n ≤ U then differencingPhase (f n) else 0

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CountingPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CountingPadding

def pad {k : ℕ} (n : Fin (k + 1) → ℕ) : Fin (k + 2) → ℕ :=
  Fin.snoc (Fin.snoc (fun i : Fin k => n i.castSucc) (n (Fin.last k) + 1))
    (n (Fin.last k) * (n (Fin.last k) + 1))

end Problem337.CountingPadding

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CubeFreeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.CubeFreeDensity

/-- Positive integers up to `N` divisible by a nontrivial integer cube. -/
def bad (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => ∃ k : ℕ, 2 ≤ k ∧ k ^ 3 ∣ n)

/-- Positive cube-free integers up to `N`. -/
def good (N : ℕ) : Finset ℕ := Finset.Icc 1 N \ bad N

@[simp] theorem mem_bad {N n : ℕ} :
    n ∈ bad N ↔ 1 ≤ n ∧ n ≤ N ∧ ∃ k : ℕ, 2 ≤ k ∧ k ^ 3 ∣ n := by
  classical
  simp only [bad, Finset.mem_filter, Finset.mem_Icc, and_assoc]

@[simp] theorem mem_good {N n : ℕ} :
    n ∈ good N ↔ 1 ≤ n ∧ n ≤ N ∧ ∀ k : ℕ, 2 ≤ k → ¬ k ^ 3 ∣ n := by
  classical
  simp only [good, Finset.mem_sdiff, Finset.mem_Icc, mem_bad]
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hbad⟩
    exact ⟨hn1, hnN, fun k hk hdiv => hbad ⟨hn1, hnN, k, hk, hdiv⟩⟩
  · rintro ⟨hn1, hnN, hfree⟩
    exact ⟨⟨hn1, hnN⟩, fun ⟨_, _, k, hk, hdiv⟩ => hfree k hk hdiv⟩

end Problem337.CubeFreeDensity

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Divisors at every multiplicative scale, in the form used by grouping. -/
def HasMarkedDivisorDensity (m q : ℕ) : Prop :=
  ∀ w : ℝ, 1 ≤ w → w ≤ (q : ℝ) →
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ w / (m : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ w

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGroupingUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A supply expresses every small integer as a short sum of rational divisors. -/
def HasRationalDivisorSupply (m K B : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 →
    ∃ terms : List (ℕ × ℕ), terms.length ≤ B ∧
      (∀ et ∈ terms, 0 < et.1 ∧ et.1 ∣ K ∧ 0 < et.2) ∧
      (terms.map (fun et => (et.1 : ℚ) / (et.2 : ℚ))).sum = (s : ℚ)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RationalDivisorSupplyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- A rational number is a sum of at most `B` positive rational summands,
whose natural numerators divide the fixed common supply `K`. -/
def HasRationalDivisorSum (K : ℕ) (x : ℚ) (B : ℕ) : Prop :=
  ∃ k : ℕ, k ≤ B ∧ ∃ e t : Fin k → ℕ,
    (∀ i, 0 < e i ∧ e i ∣ K ∧ 0 < t i) ∧
    (∑ i, (e i : ℚ) / (t i : ℚ)) = x

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CubeFreeSupplyFromExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The actual exceptional moduli: multiples of a bad divisor coprime to the
fixed supply. The unit divisor is excluded, as in the Fourier collision API. -/
def badCoprimeDivisorMultiples (N P : ℕ) (Q : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun q => ∃ d : ℕ,
    2 ≤ d ∧ d ∣ q ∧ Nat.Coprime d P ∧ ¬Q d)

@[simp] theorem mem_badCoprimeDivisorMultiples {N P q : ℕ} {Q : ℕ → Prop} :
    q ∈ badCoprimeDivisorMultiples N P Q ↔
      1 ≤ q ∧ q ≤ N ∧ ∃ d : ℕ, 2 ≤ d ∧ d ∣ q ∧ Nat.Coprime d P ∧ ¬Q d := by
  classical
  simp only [badCoprimeDivisorMultiples, Finset.mem_filter, Finset.mem_Icc, and_assoc]

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.CyclicSmoothing

/-- Convolution of a normalized nonnegative kernel with an interval (or any
finite window). -/
def window {G : Type*} [AddGroup G] (K : G → ℝ) (J : Finset G) (x : G) : ℝ :=
  ∑ y ∈ J, K (x - y)

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FejerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.GeometricKernel

/-- The nonnegative, degree-normalized squared geometric sum. -/
noncomputable def kernel (h : ℕ) (z : ℂ) : ℝ :=
  ‖∑ j ∈ Finset.range h, z ^ j‖ ^ 2 / (h : ℝ)

end Problem337.GeometricKernel

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CyclicKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate

namespace Problem337.CyclicSmoothing

/-- The kernel normalized for counting measure on `ZMod q`. -/
def normalizedKernel {q : ℕ} [NeZero q] (h : ℕ) (x : ZMod q) : ℝ :=
  GeometricKernel.kernel h (ZMod.stdAddChar x) / (q : ℝ)

end Problem337.CyclicSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GoodNumeratorSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Finite backwards construction, indexed first by the number of remaining
steps so that its recursion is structurally terminating. -/
def goodNumeratorAux
    (X : ℕ → ℝ) (I : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ → ℕ) :
    ℕ → ℕ → Finset ℕ
  | 0, j => Finset.Icc 1 ⌊X j⌋₊
  | n + 1, j => by
      classical
      exact (Finset.Icc 1 ⌊X j⌋₊).filter (fun u =>
        u ∈ goodNumeratorAux X I res n (j + 1) ∨
        ∃ i ∈ I j, res j i u = 0 ∨ res j i u ∈ goodNumeratorAux X I res n (j + 1))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The truncated divisor count appearing in the shifted moment hypothesis. -/
def densityDivisorCount (X : ℝ) (N : ℕ) : ℝ :=
  ((N.divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card : ℝ)

/-- Explicit finite arithmetic data consumed by the density descent.
No residue-distribution or divisor-moment estimate is asserted by this structure:
these are the `many_residues` and `moment_bound` fields that must be supplied. -/
structure DensityBadFamily (S m ρ r c : ℝ) (d : ℕ) where
  cutoff : ℕ → ℝ
  bad : ℕ → Finset ℕ
  exceptional : ℕ → Finset ℕ
  indices : ℕ → Finset ℕ
  residue : ℕ → ℕ → ℕ → ℕ
  shift : ℕ → ℕ → ℕ
  loss : ℝ
  loss_pos : 0 < loss
  loss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤ Real.exp (2 * S ^ (1 / 4 : ℝ))
  cutoff_pos : ∀ j ≤ d, 0 < cutoff j
  cutoff_step : ∀ j < d, cutoff (j + 1) = ρ * cutoff j
  bad_bounded : ∀ j ≤ d, bad j ⊆ Finset.Icc 1 ⌊cutoff j⌋₊
  terminal_empty : bad d = ∅
  indices_nonempty : ∀ j < d, (indices j).Nonempty
  shift_pos : ∀ j < d, ∀ i ∈ indices j, 0 < shift j i
  residue_dvd : ∀ j < d, ∀ i ∈ indices j, ∀ u ∈ bad j,
    u ∣ shift j i + residue j i u
  inherited : ∀ j < d, ∀ u ∈ bad j,
    (u : ℝ) ≤ cutoff (j + 1) → u ∈ bad (j + 1)
  many_residues : ∀ j < d, ∀ u ∈ bad j, u ∉ exceptional j →
    cutoff (j + 1) < (u : ℝ) →
    ρ * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i => residue j i u ∈ bad (j + 1))).card : ℝ)
  exception_bound : ∀ j < d,
    ((exceptional j).card : ℝ) ≤ cutoff j * Real.exp (-c * m)
  moment_bound : ∀ j < d, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff (j + 1)⌋₊,
      densityDivisorCount (cutoff j) (shift j i + h) ^ r) ≤
        cutoff (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))

/-- Raw residue data before the good sets are constructed. The terminal
expansions, small-residue supply and shifted divisor moments are explicit
inputs; all finite propagation is proved below. -/
structure DensityResidueFamily (S m ρ r c : ℝ) (d : ℕ) where
  cutoff : ℕ → ℝ
  exceptional : ℕ → Finset ℕ
  indices : ℕ → Finset ℕ
  residue : ℕ → ℕ → ℕ → ℕ
  denominator : ℕ
  factor : ℕ → ℕ
  divisor : ℕ → ℕ → ℕ
  quotient : ℕ → ℕ → ℕ → ℕ
  baseLength : ℕ
  loss : ℝ
  loss_pos : 0 < loss
  loss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤ Real.exp (2 * S ^ (1 / 4 : ℝ))
  cutoff_pos : ∀ j ≤ d, 0 < cutoff j
  cutoff_step : ∀ j < d, cutoff (j + 1) = ρ * cutoff j
  denominator_pos : 0 < denominator
  factor_pos : ∀ j ≤ d, 0 < factor j
  factor_dvd : ∀ j < d, factor (j + 1) ∣ factor j
  indices_nonempty : ∀ j < d, (indices j).Nonempty
  divisor_pos : ∀ j < d, ∀ i ∈ indices j, 0 < divisor j i
  divisor_dvd : ∀ j < d, ∀ i ∈ indices j, divisor j i ∣ denominator
  quotient_pos : ∀ j < d, ∀ i ∈ indices j, ∀ u ∈ Finset.Icc 1 ⌊cutoff j⌋₊,
    0 < quotient j i u
  residue_eq : ∀ j < d, ∀ i ∈ indices j, ∀ u ∈ Finset.Icc 1 ⌊cutoff j⌋₊,
    factor j * divisor j i + residue j i u = u * quotient j i u
  many_small_residues : ∀ j < d, ∀ u ∈ Finset.Icc 1 ⌊cutoff j⌋₊,
    u ∉ exceptional j → cutoff (j + 1) < (u : ℝ) →
    ρ * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i => (residue j i u : ℝ) ≤ cutoff (j + 1))).card : ℝ)
  exception_bound : ∀ j < d,
    ((exceptional j).card : ℝ) ≤ cutoff j * Real.exp (-c * m)
  moment_bound : ∀ j < d, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff (j + 1)⌋₊,
      densityDivisorCount (cutoff j) (factor j * divisor j i + h) ^ r) ≤
        cutoff (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))
  terminal_expansions : ∀ u ∈ Finset.Icc 1 ⌊cutoff d⌋₊,
    Descent.UnitListAtMost ((u : ℚ) / (denominator * factor d : ℕ)) baseLength

/-- The exact recursive good-set specification needed for both effects of the
construction: closure counts bad residues, and decomposition propagates lists. -/
def DensityResidueFamily.GoodSets
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityResidueFamily S m ρ r c d)
    (G : ℕ → Finset ℕ) : Prop :=
  (∀ j ≤ d, G j ⊆ Finset.Icc 1 ⌊F.cutoff j⌋₊) ∧
  G d = Finset.Icc 1 ⌊F.cutoff d⌋₊ ∧
  (∀ j < d, ∀ u : ℕ, u ∈ G j ↔
    u ∈ Finset.Icc 1 ⌊F.cutoff j⌋₊ ∧
    (u ∈ G (j + 1) ∨ ∃ i ∈ F.indices j,
      F.residue j i u = 0 ∨ F.residue j i u ∈ G (j + 1)))

/-- Every small successful index for a bad numerator lands at a bad numerator
at the next level. In particular a zero residue cannot remain bad. -/
def DensityResidueFamily.toBadFamily
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityResidueFamily S m ρ r c d)
    (G : ℕ → Finset ℕ) (hG : F.GoodSets G) : DensityBadFamily S m ρ r c d := by
  classical
  let H : ℕ → Finset ℕ := fun j => Finset.Icc 1 ⌊F.cutoff j⌋₊ \ G j
  refine {
    cutoff := F.cutoff
    bad := H
    exceptional := F.exceptional
    indices := F.indices
    residue := F.residue
    shift := fun j i => F.factor j * F.divisor j i
    loss := F.loss
    loss_pos := F.loss_pos
    loss_bound := F.loss_bound
    cutoff_pos := F.cutoff_pos
    cutoff_step := F.cutoff_step
    bad_bounded := fun j _ => Finset.sdiff_subset
    terminal_empty := ?_
    indices_nonempty := F.indices_nonempty
    shift_pos := ?_
    residue_dvd := ?_
    inherited := ?_
    many_residues := ?_
    exception_bound := F.exception_bound
    moment_bound := F.moment_bound }
  · simp [H, hG.2.1]
  · intro j hj i hi
    exact Nat.mul_pos (F.factor_pos j (by omega)) (F.divisor_pos j hj i hi)
  · intro j hj i hi u hu
    exact ⟨F.quotient j i u, F.residue_eq j hj i hi u (Finset.mem_sdiff.mp hu).1⟩
  · intro j hj u hu hlow
    obtain ⟨huI, hunG⟩ := Finset.mem_sdiff.mp hu
    apply Finset.mem_sdiff.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp huI).1, Nat.le_floor hlow⟩
    · intro huG
      exact hunG ((hG.2.2 j hj u).mpr ⟨huI, Or.inl huG⟩)
  · intro j hj u hu huE hhigh
    obtain ⟨huI, hunG⟩ := Finset.mem_sdiff.mp hu
    apply (F.many_small_residues j hj u huI huE hhigh).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hiI, hiSmall⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hiI, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · have hne : F.residue j i u ≠ 0 := by
        intro hz
        exact hunG ((hG.2.2 j hj u).mpr ⟨huI, Or.inr ⟨i, hiI, Or.inl hz⟩⟩)
      exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_floor hiSmall⟩
    · intro hiG
      exact hunG ((hG.2.2 j hj u).mpr ⟨huI, Or.inr ⟨i, hiI, Or.inr hiG⟩⟩)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337.ResidueLevels

/-- The first index at which a geometric scale reaches `exp m`. -/
def depth (A m η : ℝ) : ℕ := ⌈(A - m) / (η * m)⌉₊

/-- A geometric scale, kept in logarithmic coordinates. -/
def level (A m η : ℝ) (j : ℕ) : ℝ := Real.exp (A - η * m * j)

theorem level_pos (A m η : ℝ) (j : ℕ) : 0 < level A m η j :=
  Real.exp_pos _

theorem level_strictAnti {A m η : ℝ} (hm : 0 < m) (hη : 0 < η) :
    StrictAnti (level A m η) := by
  intro i j hij
  apply Real.exp_lt_exp.mpr
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have := mul_lt_mul_of_pos_left hijR (mul_pos hη hm)
  linarith

theorem final_level_bounds {A m η : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) :
    Real.exp ((1 - η) * m) < level A m η (depth A m η) ∧
      level A m η (depth A m η) ≤ Real.exp m := by
  have hp : 0 < η * m := mul_pos hη hm
  have hx : 0 ≤ (A - m) / (η * m) := div_nonneg (sub_nonneg.mpr hA) hp.le
  have hl := Nat.le_ceil ((A - m) / (η * m))
  have hu := Nat.ceil_lt_add_one hx
  change (A - m) / (η * m) ≤ (depth A m η : ℝ) at hl
  change (depth A m η : ℝ) < (A - m) / (η * m) + 1 at hu
  have hl' := (div_le_iff₀ hp).1 hl
  have hu' := mul_lt_mul_of_pos_right hu hp
  rw [add_mul, div_mul_cancel₀ _ hp.ne'] at hu'
  constructor
  · apply Real.exp_lt_exp.mpr
    nlinarith
  · apply Real.exp_le_exp.mpr
    nlinarith

/-- The auxiliary denominator factor changes only from `C` to `1`. -/
def factor (A m η S : ℝ) (C j : ℕ) : ℕ :=
  if Real.exp S < level A m η j then C else 1

theorem next_factor_dvd {A m η S : ℝ} (hm : 0 < m) (hη : 0 < η)
    (C j : ℕ) : factor A m η S C (j + 1) ∣ factor A m η S C j := by
  unfold factor
  split_ifs with hnext hcur hcur
  · exact dvd_refl C
  · have hdec := level_strictAnti (A := A) hm hη (Nat.lt_succ_self j)
    exact False.elim (hcur (hnext.trans hdec))
  · exact one_dvd C
  · exact dvd_refl 1

/-- The integer number of prime factors used at scale `S`. -/
def scale (S : ℝ) : ℕ := ⌊S / Real.log S⌋₊

@[simp] theorem level_zero (A m η : ℝ) : level A m η 0 = Real.exp A := by
  simp [level]

theorem level_succ (A m η : ℝ) (j : ℕ) :
    level A m η (j + 1) = Real.exp (-η * m) * level A m η j := by
  simp only [level, Nat.cast_add, Nat.cast_one, ← Real.exp_add]
  congr 1
  ring

theorem final_factor_one {A m η S : ℝ} (hm : 0 < m) (hη : 0 < η)
    (hA : m ≤ A) (hmS : m ≤ S) (C : ℕ) :
    factor A m η S C (depth A m η) = 1 := by
  have hfinal := (final_level_bounds hm hη hA).2
  have hle : level A m η (depth A m η) ≤ Real.exp S :=
    hfinal.trans (Real.exp_le_exp.mpr hmS)
  simp only [factor, not_lt.mpr hle, ↓reduceIte]

/-- Every auxiliary factor is positive once the initial factor is. -/
theorem factor_pos {A m η S : ℝ} {C : ℕ} (hC : 0 < C) (j : ℕ) :
    0 < factor A m η S C j := by
  unfold factor
  split_ifs <;> omega

/-- The floor scale lies below the original scale; this is the missing
comparison needed to certify that the terminal auxiliary factor equals one. -/
theorem scale_le_self {S : ℝ} (hS : 0 ≤ S) (hlog : 1 ≤ Real.log S) :
    (scale S : ℝ) ≤ S := by
  have hlogpos : 0 < Real.log S := by linarith
  have hratio : 0 ≤ S / Real.log S := div_nonneg hS hlogpos.le
  apply (Nat.floor_le hratio).trans
  apply (div_le_iff₀ hlogpos).2
  nlinarith

end Problem337.ResidueLevels

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- A common exponential size parameter for cutoffs and translated divisors. -/
def densityMomentParameter (DM : ℝ) : ℝ := 8 * (DM + 2) + DM + 1

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DiscreteFirstDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.ExponentialSum

noncomputable def phase (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

noncomputable def phaseWeight (x : ℝ) : ℂ :=
  -(1 : ℂ) / 2 - (Real.cot (Real.pi * x) : ℂ) * Complex.I / 2

end Problem337.ExponentialSum

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DyadicBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DyadicBands

/-- A half-open band on a multiplicative dyadic scale. -/
def InBand (a : ℝ) (j : ℕ) (x : ℝ) : Prop :=
  a * 2 ^ j ≤ x ∧ x < a * 2 ^ (j + 1)

instance instDecidableInBand (a : ℝ) (j : ℕ) (x : ℝ) : Decidable (InBand a j x) := by
  unfold InBand
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Number of dyadic bands needed to cover `[a,B]`. -/
def bandCount (a B : ℝ) : ℕ :=
  ⌊Real.log (B / a) / Real.log 2⌋₊ + 1

end Problem337.DyadicBands

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorClasses

attribute [local instance] Classical.propDecidable

/-- The selected sorted prime-factor prefix, including both separation facts. -/
def PrefixWitness (n : ℕ) (Y : ℝ) (d p : ℕ) : Prop :=
  0 < d ∧ p.Prime ∧ d ∣ n ∧ (d : ℝ) ≤ Real.sqrt Y ∧
    Real.sqrt Y < (d * p : ℕ) ∧ p ∣ n / d ∧
    (∀ q : ℕ, q.Prime → q ∣ d → q ≤ p) ∧
    (∀ q : ℕ, q.Prime → q ∣ n / d → p ≤ q)

def LargeClass (n : ℕ) (v Y : ℝ) : Prop :=
  (n : ℝ) ≤ Real.sqrt Y ∨ ∃ d p : ℕ,
    PrefixWitness n Y d p ∧ v ^ (15 / 16 : ℝ) ≤ Real.log p

def SmallClass (n : ℕ) (S v Y : ℝ) : Prop :=
  ∃ d p : ℕ, PrefixWitness n Y d p ∧
    Real.log p < v ^ (15 / 16 : ℝ) ∧ Real.log p < 4 * Real.log S

def BandClass (n : ℕ) (S v Y : ℝ) (j : ℕ) : Prop :=
  ∃ d p : ℕ, PrefixWitness n Y d p ∧
    Real.log p < v ^ (15 / 16 : ℝ) ∧
    DyadicBands.InBand (4 * Real.log S) j (Real.log p)

end Problem337.DivisorClasses

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- A positive integer has a divisor within a factor of `m` below each scale. -/
def DivisorDense (m q : ℕ) : Prop :=
  ∀ w : ℝ, 1 ≤ w → w ≤ (q : ℝ) →
    ∃ d : ℕ, 0 < d ∧ d ∣ q ∧ w / (m : ℝ) ≤ (d : ℝ) ∧ (d : ℝ) ≤ w

/-- Denominators produced by multiplying by positive integers at most one
more than the preceding denominator, without reducing fractions. -/
inductive GreedyDenominator (m : ℕ) : ℕ → Prop
  | base : GreedyDenominator m m
  | mul {q n : ℕ} : GreedyDenominator m q → 1 ≤ n → n ≤ q + 1 →
      GreedyDenominator m (n * q)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorMomentAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter Asymptotics

namespace Problem337.DivisorMomentAbsorption

/-- Explicit coefficients for converting the uniform large-prime class estimate
into the form required by `eventually_divisor_moment_absorption`. -/
def largeCoefficient (D r : ℝ) : ℝ :=
  r * (2 + Real.log (2 * (D + 1))) * D ^ (1 / 16 : ℝ)

def harmonicCoefficient (D C : ℝ) : ℝ :=
  C * (1 + Real.log (D + 1)) + Real.log 2

end Problem337.DivisorMomentAbsorption

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorPointwiseUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- An explicit uniform error coefficient for the pointwise truncated-divisor estimate. -/
def divisorPointwiseError (E S : ℝ) : ℝ :=
  4 * (Real.log S) ^ 2 / Real.sqrt S +
    2 * (1 + Real.log (2 * E) + Real.log (Real.log S)) / Real.log S

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DivisorSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The larger denominator in the split of `1 / n` indexed by `d ∣ n`. -/
def divisorSplitUpper (n d : ℕ) : ℕ := (n / d) * (n + d)

/-- A split is good when neither new denominator collides with an unchanged term. -/
def countingGoodSplitDivisors (n : ℕ) (s : Finset ℕ) : Finset ℕ :=
  n.properDivisors.filter (fun d => n + d ∉ s ∧ divisorSplitUpper n d ∉ s)

/-- Append the two denominators indexed by a divisor to a fixed unchanged set. -/
def countingDivisorSplitSet (n d : ℕ) (s : Finset ℕ) : Finset ℕ :=
  insert (n + d) (insert (divisorSplitUpper n d) s)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_EightProductConductor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-!
# Eight products from a subuniform conductor collision bound

A collision exponent of `7/8`, unlike exact equidistribution, is compatible
with the rough-modulus exceptional-set construction. Eight products then
produce a cubic conductor loss, controlled by the existing uniform `3/4`
conductor budget. The index type retains all sample multiplicities.
-/

noncomputable section
open scoped BigOperators

namespace Problem337.CompositeSpectral

/-- Ordered residue-collision pairs, expressed with natural remainders so
no typeclass proof is part of the collision function's data. -/
def remainderCollisionCount {ι : Type*} [Fintype ι] (t : ι → ℕ) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun ij : ι × ι => t ij.1 % d = t ij.2 % d)).card

end Problem337.CompositeSpectral

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ExactPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Algebraic interface needed to rule out the two exceptional splits at a prime. -/
def PrimePaddingObstruction : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 3 ≤ p → ∀ (t : Finset ℕ),
    (∀ x ∈ t, 1 ≤ x ∧ x < p) → ∀ v : ℕ,
    (∑ x ∈ t, (1 : ℚ) / x) + 1 / p + 1 / v = 1 →
    v ≠ p + 1 ∧ v ≠ p * (p + 1)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteEulerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- The multiplicative weight used in harmonic and Rankin divisor moments. -/
def divisorMomentWeight (r : ℕ) (σ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n.divisors.card : ℝ) ^ r * (n : ℝ) ^ (-σ), by simp⟩

end Problem337.DivisorMoment

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteResidueIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Natural indices for a finite sample space. Distinct samples remain distinct
indices even when their integer-valued data agree. -/
def residueIndices (α : Type*) [Fintype α] : Finset ℕ :=
  Finset.range (Fintype.card α)

/-- Extend finite sample data by zero outside their canonical natural indices. -/
def residueEntry {α β : Type*} [Fintype α] [Zero β] (f : α → β) (i : ℕ) : β :=
  if hi : i < Fintype.card α then f ((Fintype.equivFin α).symm ⟨i, hi⟩) else 0

@[simp] theorem residueIndices_card (α : Type*) [Fintype α] :
    (residueIndices α).card = Fintype.card α := by
  simp [residueIndices]

@[simp] theorem mem_residueIndices {α : Type*} [Fintype α] {i : ℕ} :
    i ∈ residueIndices α ↔ i < Fintype.card α := by
  simp [residueIndices]

@[simp] theorem residueEntry_equivFin {α β : Type*} [Fintype α] [Zero β]
    (f : α → β) (a : α) :
    residueEntry f (Fintype.equivFin α a).val = f a := by
  simp [residueEntry]

/-- Nonemptiness transfers without any injectivity requirement on the data. -/
@[simp] theorem residueIndices_nonempty_iff (α : Type*) [Fintype α] :
    (residueIndices α).Nonempty ↔ Nonempty α := by
  rw [← Finset.card_pos, residueIndices_card, Fintype.card_pos_iff]

/-- Function-valued residue or quotient data commute with evaluation. -/
@[simp] theorem residueEntry_apply {α β γ : Type*} [Fintype α] [Zero γ]
    (f : α → β → γ) (i : ℕ) (b : β) :
    residueEntry f i b = residueEntry (fun a => f a b) i := by
  unfold residueEntry
  split <;> rfl

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FixedSumFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Ordered positive denominator tuples with a prescribed rational sum.
Repetitions are allowed. -/
def OrderedUnitSums (k : ℕ) (x : ℚ) : Set (Fin k → ℕ) :=
  {n | (∀ i, 0 < n i) ∧ Monotone n ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = x}

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricRandomRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337.GeometricRandomRanges

/-- The common geometric cutoffs used in the random middle-level selection. -/
def cutoff (D S : ℝ) (j : ℕ) : ℝ :=
  ResidueLevels.level (D * S) (ResidueLevels.scale S) (1 / 10000) j

/-- Only levels whose denominator factor is one need a random block. -/
def middleTests (D S : ℝ) : Finset ℕ :=
  (Finset.range (ResidueLevels.depth (D * S) (ResidueLevels.scale S) (1 / 10000))).filter
    (fun j => cutoff D S j ≤ Real.exp S)

/-- Positive integers in the open-closed interval between adjacent cutoffs. -/
def middleLevel (D S : ℝ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊cutoff D S j⌋₊).filter
    (fun u => cutoff D S (j + 1) < (u : ℝ))

/-- The terminal numerators not covered by the binary factor. -/
def terminalRange (S : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊Real.exp (ResidueLevels.scale S)⌋₊).filter
    (fun u => S ^ 100000 < (u : ℝ))

/-- All non-arithmetic hypotheses of the common sampled-Fourier selection,
for the actual geometric middle levels and terminal interval. The finite
indices retain multiplicity; no residue or cancellation bound is assumed. -/
structure SelectionRanges (D S : ℝ) (N : ℕ) : Prop where
  parameter_large : 8 ≤ S
  scale_large : 500000 ≤ (ResidueLevels.scale S : ℝ)
  tests_card : ((middleTests D S).card : ℝ) ≤ (ResidueLevels.scale S : ℝ)
  cutoff_positive : ∀ j ∈ middleTests D S, 0 < cutoff D S j
  level_card : ∀ j ∈ middleTests D S, ((middleLevel D S j).card : ℝ) ≤ cutoff D S j
  middle_window : ∀ j ∈ middleTests D S, ∀ u ∈ middleLevel D S j,
    100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
      (9999 / 10000 : ℝ) * (ResidueLevels.scale S : ℝ) ≤ Real.log (u : ℝ)
  terminal_threshold : ∀ u ∈ terminalRange S, N ≤ u
  terminal_window : ∀ u ∈ terminalRange S,
    100000 * Real.log S ≤ Real.log (u : ℝ) ∧
      Real.log (u : ℝ) ≤ (ResidueLevels.scale S : ℝ)

end Problem337.GeometricRandomRanges

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GreedyPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A prefix ending either at zero or at a denominator in the target window. -/
def PreparedGreedyPrefix (a b : ℕ) (T : ℝ) (N : ℕ) : Prop :=
  ∃ (l : List ℕ) (A C : ℕ),
    l.length ≤ N ∧ (∀ d ∈ l, 2 ≤ d) ∧ A ≤ a ∧ 0 < C ∧
    (l.map (fun d => (1 : ℚ) / (d : ℚ))).sum + (A : ℚ) / (C : ℚ) =
      (a : ℚ) / (b : ℚ) ∧
    (A = 0 ∨ (1 ≤ A ∧ T ≤ (C : ℝ) ∧ (C : ℝ) < T ^ 2))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MainUpperReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- The exact dense-family input required by the elementary main upper reduction.
No distinctness is asked of the supplied lists. -/
def DenseEgyptianFamily (DM L S : ℝ) (C : ℕ) : Prop :=
  ∃ (M : ℕ) (G : Finset ℕ),
    Real.exp S < (M : ℝ) ∧ (M : ℝ) ≤ Real.exp (DM * S) ∧
    ((Finset.Icc 1 ⌊Real.exp ((DM + 2) * S)⌋₊ \ G).card : ℝ) ≤
      Real.exp ((DM + 2) * S) / 8 ∧
    ∀ u ∈ G, ∃ ds : List ℕ,
      (∀ d ∈ ds, 2 ≤ d) ∧ (ds.length : ℝ) ≤ L * Real.log S ∧
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (u : ℚ) / ((M * C : ℕ) : ℚ)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RawDensityUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The remaining arithmetic supply interface for the main upper bound.
The residue distribution and shifted divisor moments are explicit fields of
`DensityResidueFamily`; this definition does not assert their existence. -/
def RawDensitySupply (DM L c K r S : ℝ) (C : ℕ) : Prop :=
  ∃ (m ρ : ℝ) (d : ℕ) (F : DensityResidueFamily S m ρ r c d),
    S / (2 * Real.log S) ≤ m ∧ (d : ℝ) ≤ K * Real.log S ∧
    0 < ρ ∧ ρ ≤ 1 ∧
    ((F.baseLength + d : ℕ) : ℝ) ≤ L * Real.log S ∧
    F.cutoff 0 = Real.exp ((DM + 2) * S) ∧ F.factor 0 = C ∧
    Real.exp S < (F.denominator : ℝ) ∧
    (F.denominator : ℝ) ≤ Real.exp (DM * S)

end Problem337


end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TerminalDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337.TerminalDepth

/-- Number of contractions reducing a logarithmic height `S` to one. -/
def depth (α S : ℝ) : ℕ := ⌈Real.log S / (-Real.log α)⌉₊

theorem depth_contracts {α S : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) : α ^ depth α S * S ≤ 1 := by
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hSpos : 0 < S := by linarith
  have hceil : Real.log S ≤ (depth α S : ℝ) * (-Real.log α) :=
    (div_le_iff₀ hlogα).1 (Nat.le_ceil _)
  have hpowpos : 0 < α ^ depth α S := pow_pos hα _
  apply (Real.log_le_log_iff (mul_pos hpowpos hSpos) (by norm_num : (0 : ℝ) < 1)).1
  rw [Real.log_mul (ne_of_gt hpowpos) (ne_of_gt hSpos), Real.log_pow, Real.log_one]
  nlinarith

/-- The base-two exponent needed by the terminal binary range. -/
def binaryExponent (D S : ℝ) : ℕ := ⌈D * Real.log S / Real.log 2⌉₊

theorem binary_log_lower {D S : ℝ} (hD : 1 ≤ D) (hlogS : 1 ≤ Real.log S) :
    1 ≤ Real.log ((2 : ℝ) ^ binaryExponent D S) := by
  rw [Real.log_pow]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : D * Real.log S ≤ (binaryExponent D S : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).1 (Nat.le_ceil _)
  nlinarith

theorem terminal_length_budget {D α S : ℝ} (hD : 1 ≤ D)
    (hα : 0 < α) (hα1 : α < 1) (hlogS : 1 ≤ Real.log S) :
    ((binaryExponent D S + 1 + depth α S : ℕ) : ℝ) ≤
      (D / Real.log 2 + 1 / (-Real.log α) + 3) * Real.log S := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogα : 0 < -Real.log α := neg_pos.2 (Real.log_neg hα hα1)
  have hD0 : 0 ≤ D := by linarith
  have hS0 : 0 ≤ Real.log S := by linarith
  have ha : (binaryExponent D S : ℝ) < D * Real.log S / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hD0 hS0) hlog2.le)
  have hd : (depth α S : ℝ) < Real.log S / (-Real.log α) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hS0 hlogα.le)
  push_cast
  calc
    (binaryExponent D S : ℝ) + 1 + depth α S ≤
        D * Real.log S / Real.log 2 + Real.log S / (-Real.log α) + 3 := by linarith
    _ ≤ (D / Real.log 2 + 1 / (-Real.log α) + 3) * Real.log S := by
      rw [add_mul, add_mul]
      have h1 : D / Real.log 2 * Real.log S = D * Real.log S / Real.log 2 := by ring
      have h2 : 1 / (-Real.log α) * Real.log S = Real.log S / (-Real.log α) := by ring
      rw [h1, h2]
      linarith

theorem potential_bound {α S : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) (u : ℕ) (hu : (u : ℝ) ≤ Real.exp S) :
    α ^ depth α S * Real.log (u : ℝ) ≤ 1 := by
  by_cases hu0 : u = 0
  · subst u
    norm_num
  have hupos : (0 : ℝ) < u := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
  have hlogu : Real.log (u : ℝ) ≤ S := (Real.log_le_iff_le_exp hupos).2 hu
  exact (mul_le_mul_of_nonneg_left hlogu (pow_nonneg hα.le _)).trans
    (depth_contracts hα hα1 hS)

theorem rpow_le_binary {D S : ℝ} (hS : 0 < S) :
    S ^ D ≤ (2 : ℝ) ^ binaryExponent D S := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : D * Real.log S ≤ (binaryExponent D S : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).1 (Nat.le_ceil _)
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hS D) (by positivity)).1
  rw [Real.log_rpow hS, Real.log_pow]
  exact hceil

end Problem337.TerminalDepth

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TerminalRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.TerminalDescent

/-- Unit-fraction lists in the intermediate construction may repeat denominators. -/
def UnitList (x : ℚ) (s : List ℕ) : Prop :=
  (∀ d ∈ s, 0 < d) ∧ (s.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = x

lemma reciprocal_sum_scale (s : List ℕ) (z : ℕ) :
    ((s.map (fun d => z * d)).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
      (s.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum / (z : ℚ) := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_mul, ih, add_div]
    rw [div_div, mul_comm (z : ℚ)]

lemma UnitList.scale {x : ℚ} {s : List ℕ} (hs : UnitList x s)
    {z : ℕ} (hz : 0 < z) :
    UnitList (x / (z : ℚ)) (s.map (fun d => z * d)) := by
  constructor
  · intro d hd
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
    exact Nat.mul_pos hz (hs.1 a ha)
  · rw [reciprocal_sum_scale, hs.2]

lemma unitList_zero : UnitList 0 [] := by simp [UnitList]

/-- A power-saving step contracts the logarithmic potential. -/
lemma log_potential_step {u h q : ℝ} (hu : 0 < u) (hh : 0 < h)
    (hq : 0 ≤ q) (hstep : h ≤ u ^ q) (N : ℕ) :
    q ^ N * Real.log h ≤ q ^ (N + 1) * Real.log u := by
  have hr := Real.log_le_log hh hstep
  rw [Real.log_rpow hu] at hr
  calc
    q ^ N * Real.log h ≤ q ^ N * (q * Real.log u) :=
      mul_le_mul_of_nonneg_left hr (pow_nonneg hq N)
    _ = q ^ (N + 1) * Real.log u := by rw [pow_succ]; ring

/-- Terminal descent: each residue step adds one unit fraction; the
logarithmic contraction gives an explicit upper bound on the depth. -/
theorem short_unit_list_of_descent
    (M T U B : ℕ) (hT : 0 < T) (q : ℝ) (hq : 0 ≤ q)
    (hbase : ∀ u : ℕ, u ≤ U → u ≤ T →
      ∃ s : List ℕ, UnitList ((u : ℚ) / (M : ℚ)) s ∧ s.length ≤ B)
    (hstep : ∀ u : ℕ, u ≤ U → T < u →
      ∃ a z h : ℕ, 0 < a ∧ 0 < z ∧ h ≤ U ∧
        (h : ℝ) ≤ (u : ℝ) ^ q ∧
        (u : ℚ) / (M : ℚ) = (1 : ℚ) / (a : ℚ) +
          ((h : ℚ) / (M : ℚ)) / (z : ℚ)) :
    ∀ N u : ℕ, u ≤ U →
      q ^ N * Real.log (u : ℝ) ≤ Real.log (T : ℝ) →
      ∃ s : List ℕ, UnitList ((u : ℚ) / (M : ℚ)) s ∧ s.length ≤ B + N := by
  intro N
  induction N with
  | zero =>
    intro u hu hpot
    have huT : u ≤ T := by
      by_cases hu0 : u = 0
      · omega
      have huR : (0 : ℝ) < u := by exact_mod_cast (Nat.pos_of_ne_zero hu0)
      have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      simp only [pow_zero, one_mul] at hpot
      exact_mod_cast (Real.log_le_log_iff huR hTR).mp hpot
    simpa using hbase u hu huT
  | succ N ih =>
    intro u hu hpot
    by_cases huT : u ≤ T
    · obtain ⟨s, hs, hlen⟩ := hbase u hu huT
      exact ⟨s, hs, by omega⟩
    have hTu : T < u := by omega
    obtain ⟨a, z, h, ha, hz, hhU, hsmall, hid⟩ := hstep u hu hTu
    have hex : ∃ s : List ℕ, UnitList ((h : ℚ) / (M : ℚ)) s ∧
        s.length ≤ B + N := by
      by_cases hh0 : h = 0
      · subst h
        exact ⟨[], by simpa using unitList_zero, by simp⟩
      apply ih h hhU
      have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
      have hhR : (0 : ℝ) < h := by exact_mod_cast (Nat.pos_of_ne_zero hh0)
      exact (log_potential_step huR hhR hq hsmall N).trans hpot
    obtain ⟨s, hs, hlen⟩ := hex
    refine ⟨a :: s.map (fun d => z * d), ?_, ?_⟩
    · constructor
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ha
        · exact (hs.scale hz).1 d hd
      · simp only [List.map_cons, List.sum_cons]
        rw [(hs.scale hz).2]
        exact hid.symm
    · simp only [List.length_cons, List.length_map]
      omega

end Problem337.TerminalDescent

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TerminalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337.TerminalAssembly

/-- The constructive terminal stage of the dense-family argument, with an
explicit logarithmic length bound. The only remaining number-theoretic input
is the asserted supply of divisor residues. -/
theorem terminal_expansion_of_residue_supply
    (M U : ℕ) (D α S : ℝ) (hUM : U < M)
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) (hlogS : 1 ≤ Real.log S)
    (hU : (U : ℝ) ≤ Real.exp S)
    (hdiv : 2 ^ TerminalDepth.binaryExponent D S ∣ M)
    (hstep : ∀ u : ℕ, u ≤ U → S ^ D < (u : ℝ) →
      ∃ t z h : ℕ, 0 < t ∧ 0 < z ∧ t ∣ M ∧
        (h : ℝ) ≤ (u : ℝ) ^ α ∧ t + h = u * z) :
    ∀ u : ℕ, u ≤ U → ∃ l : List ℕ,
      (∀ n ∈ l, 2 ≤ n) ∧
      (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = (u : ℚ) / M ∧
      (l.length : ℝ) ≤
        (D / Real.log 2 + 1 / (-Real.log α) + 3) * Real.log S := by
  let a := TerminalDepth.binaryExponent D S
  let T := 2 ^ a
  have hT : 0 < T := by dsimp [T]; positivity
  have hM : 0 < M := by omega
  have hbase : ∀ u : ℕ, u ≤ U → u ≤ T →
      ∃ l : List ℕ, TerminalDescent.UnitList ((u : ℚ) / M) l ∧ l.length ≤ a + 1 := by
    intro u hu huT
    have hpow : u < 2 ^ (a + 1) := by
      have : 0 < 2 ^ a := by positivity
      dsimp [T] at huT
      rw [pow_succ]
      omega
    obtain ⟨l, hl2, hlen, hsum⟩ := binary_unit_fraction_list u M a (hu.trans_lt hUM) hpow hdiv
    exact ⟨l, ⟨fun n hn => by have := hl2 n hn; omega, hsum⟩, hlen⟩
  have hstep' : ∀ u : ℕ, u ≤ U → T < u →
      ∃ d z h : ℕ, 0 < d ∧ 0 < z ∧ h ≤ U ∧ (h : ℝ) ≤ (u : ℝ) ^ α ∧
      (u : ℚ) / M = (1 : ℚ) / d + ((h : ℚ) / M) / z := by
    intro u hu huT
    have hSu : S ^ D < (u : ℝ) := by
      have hb := TerminalDepth.rpow_le_binary (D := D) (by linarith : 0 < S)
      have hTuR : (T : ℝ) < u := by exact_mod_cast huT
      have hb' : S ^ D ≤ (T : ℝ) := by
        simpa only [T, a, Nat.cast_pow, Nat.cast_ofNat] using hb
      exact hb'.trans_lt hTuR
    obtain ⟨t, z, h, ht, hz, htM, hsmall, heq⟩ := hstep u hu hSu
    have hupos : 1 ≤ u := by omega
    have hhu : h ≤ u := by
      have hpow : (u : ℝ) ^ α ≤ u := by
        simpa using Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hupos : (1 : ℝ) ≤ u) hα1.le
      exact_mod_cast hsmall.trans hpow
    have hhU := hhu.trans hu
    refine ⟨(M / t) * z, z, h,
      Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd hM htM) ht) hz, hz, hhU, hsmall, ?_⟩
    have hid := residue_step_identity M 1 u t z h hM (by omega) ht hz htM (by simpa using heq)
    simpa only [mul_one, Nat.cast_mul, Nat.cast_one, one_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hid
  intro u hu
  have hlogT : 1 ≤ Real.log (T : ℝ) := by
    simpa only [T, Nat.cast_pow, Nat.cast_ofNat] using TerminalDepth.binary_log_lower hD hlogS
  have hpotential : α ^ TerminalDepth.depth α S * Real.log (u : ℝ) ≤ Real.log (T : ℝ) :=
    (TerminalDepth.potential_bound hα hα1 hS u
      ((by exact_mod_cast hu : (u : ℝ) ≤ U).trans hU)).trans hlogT
  obtain ⟨l, hl, hlen⟩ := TerminalDescent.short_unit_list_of_descent
    M T U (a + 1) hT α hα.le hbase hstep' (TerminalDepth.depth α S) u hu hpotential
  refine ⟨l, ?_, hl.2, ?_⟩
  · intro n hn
    have hn0 := hl.1 n hn
    by_contra hn2
    have hn1 : n = 1 := by omega
    subst n
    have hle : (1 : ℚ) ≤ (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum := by
      apply List.single_le_sum
      · intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
        positivity
      · exact List.mem_map.2 ⟨1, hn, by norm_num⟩
    rw [hl.2] at hle
    have hlt : (u : ℚ) / M < 1 := by
      apply (div_lt_one (by exact_mod_cast hM : (0 : ℚ) < M)).2
      exact_mod_cast hu.trans_lt hUM
    linarith
  · have hlenR : (l.length : ℝ) ≤ ((a + 1 + TerminalDepth.depth α S : ℕ) : ℝ) := by
      exact_mod_cast hlen
    exact hlenR.trans (TerminalDepth.terminal_length_budget hD hα hα1 hlogS)

end Problem337.TerminalAssembly

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TerminalBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.Descent

/-- Convert an ordinary positive list to the finite-tuple interface used by
backward propagation, without changing its length or reciprocal sum. -/
theorem UnitListAtMost.of_list {x : ℚ} {B : ℕ} (l : List ℕ)
    (hlen : l.length ≤ B) (hpos : ∀ n ∈ l, 0 < n)
    (hsum : (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x) :
    UnitListAtMost x B := by
  refine ⟨l.length, hlen, l.get, fun i => hpos _ (l.get_mem i), ?_⟩
  calc
    (∑ i : Fin l.length, (1 : ℚ) / (l.get i : ℚ)) =
        (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum := by
      rw [← List.sum_ofFn]
      change (List.ofFn ((fun n : ℕ => (1 : ℚ) / (n : ℚ)) ∘ l.get)).sum = _
      rw [← List.map_ofFn, List.ofFn_get]
    _ = x := hsum

/-- A real-valued length budget can be rounded once at the terminal stage. -/
theorem UnitListAtMost.of_list_real {x : ℚ} {L : ℝ} (l : List ℕ)
    (hlen : (l.length : ℝ) ≤ L) (hpos : ∀ n ∈ l, 0 < n)
    (hsum : (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x) :
    UnitListAtMost x ⌈L⌉₊ := by
  apply UnitListAtMost.of_list l _ hpos hsum
  exact_mod_cast hlen.trans (Nat.le_ceil L)

end Problem337.Descent

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_TerminalFiniteBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337.TerminalAssembly

/-- The fixed coefficient in the constructive terminal length estimate. -/
def terminalCoefficient (D α : ℝ) : ℝ :=
  D / Real.log 2 + 1 / (-Real.log α) + 3

/-- Direct finite-tuple terminal data for a real cutoff.  The residue hypothesis
is the genuine arithmetic input; no intermediate expansions are assumed. -/
theorem terminal_finite_expansions
    (M : ℕ) (X D α S : ℝ) (hX : 0 ≤ X)
    (hXM : X < (M : ℝ)) (hXS : X ≤ Real.exp S)
    (hD : 1 ≤ D) (hα : 0 < α) (hα1 : α < 1)
    (hS : 1 ≤ S) (hlogS : 1 ≤ Real.log S)
    (hdiv : 2 ^ TerminalDepth.binaryExponent D S ∣ M)
    (hstep : ∀ u : ℕ, (u : ℝ) ≤ X → S ^ D < (u : ℝ) →
      ∃ t z h : ℕ, 0 < t ∧ 0 < z ∧ t ∣ M ∧
        (h : ℝ) ≤ (u : ℝ) ^ α ∧ t + h = u * z) :
    ∀ u ∈ Finset.Icc 1 ⌊X⌋₊,
      Descent.UnitListAtMost ((u : ℚ) / M)
        ⌈terminalCoefficient D α * Real.log S⌉₊ := by
  have hUM : ⌊X⌋₊ < M := by
    exact_mod_cast (Nat.floor_le hX).trans_lt hXM
  have hUS : (⌊X⌋₊ : ℝ) ≤ Real.exp S := (Nat.floor_le hX).trans hXS
  have hstep' : ∀ u : ℕ, u ≤ ⌊X⌋₊ → S ^ D < (u : ℝ) →
      ∃ t z h : ℕ, 0 < t ∧ 0 < z ∧ t ∣ M ∧
        (h : ℝ) ≤ (u : ℝ) ^ α ∧ t + h = u * z := by
    intro u hu
    exact hstep u ((Nat.cast_le.mpr hu).trans (Nat.floor_le hX))
  intro u hu
  obtain ⟨l, hl, hsum, hlen⟩ := terminal_expansion_of_residue_supply M ⌊X⌋₊ D α S
    hUM hD hα hα1 hS hlogS hUS hdiv hstep' u (Finset.mem_Icc.mp hu).2
  apply Descent.UnitListAtMost.of_list_real l hlen
  · intro n hn
    have := hl n hn
    omega
  · exact hsum

end Problem337.TerminalAssembly

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GeometricRawDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter
open scoped BigOperators

namespace Problem337

/-- A positive integer shift has a positive natural ceiling quotient. -/
lemma positive_ceiling_quotient {N u : ℕ} (hN : 0 < N) (hu : 0 < u) :
    0 < ⌈(N : ℝ) / u⌉₊ := by
  have hNu : (0 : ℝ) < (N : ℝ) / u := div_pos (by exact_mod_cast hN)
    (by exact_mod_cast hu)
  exact Nat.ceil_pos.mpr hNu

/-- A normalized small negative residue gives the unnormalized ceiling bound
used by the backward construction. The cutoff need not be integral. -/
lemma ceiling_residue_le_of_fract_lt {N u : ℕ} {ρ X : ℝ}
    (hu : 0 < u) (hρ : 0 ≤ ρ) (huX : (u : ℝ) ≤ X)
    (hsmall : Int.fract (-(N : ℝ) / u) < ρ) :
    ((u * ⌈(N : ℝ) / u⌉₊ - N : ℕ) : ℝ) ≤ ρ * X := by
  rw [← natural_ceil_residue_div_eq_fract_neg u N hu] at hsmall
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  exact ((div_lt_iff₀ huR).mp hsmall).le.trans
    (mul_le_mul_of_nonneg_left huX hρ)

namespace GeometricDensity

abbrev depth (DM η S : ℝ) : ℕ :=
  ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η

abbrev cutoff (DM η S : ℝ) (j : ℕ) : ℝ :=
  ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j

abbrev factor (DM η S : ℝ) (C j : ℕ) : ℕ :=
  ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j

abbrev contraction (η S : ℝ) : ℝ := Real.exp (-η * ResidueLevels.scale S)

/-- Arithmetic residue information on the canonical geometric levels.
The normalized Fourier conclusion, exceptional count, shifted-divisor moment,
and terminal shrinking residue remain explicit hypotheses. All geometric
alignment, ceiling equations, and expansion construction are supplied below. -/
structure NormalizedResidueData (DM D₀ η c r S loss : ℝ) (C M : ℕ) where
  indices : ℕ → Finset ℕ
  divisor : ℕ → ℕ → ℕ
  exceptional : ℕ → Finset ℕ
  indices_nonempty : ∀ j < depth DM η S, (indices j).Nonempty
  divisor_pos : ∀ j < depth DM η S, ∀ i ∈ indices j, 0 < divisor j i
  divisor_dvd : ∀ j < depth DM η S, ∀ i ∈ indices j, divisor j i ∣ M
  many_residues : ∀ j < depth DM η S, ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊,
    u ∉ exceptional j → cutoff DM η S (j + 1) < (u : ℝ) →
    contraction η S * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i =>
        Int.fract (-((factor DM η S C j * divisor j i : ℕ) : ℝ) / u) <
          contraction η S)).card : ℝ)
  exception_bound : ∀ j < depth DM η S,
    ((exceptional j).card : ℝ) ≤ cutoff DM η S j *
      Real.exp (-c * ResidueLevels.scale S)
  moment_bound : ∀ j < depth DM η S, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff DM η S (j + 1)⌋₊,
      densityDivisorCount (cutoff DM η S j)
        (factor DM η S C j * divisor j i + h) ^ r) ≤
      cutoff DM η S (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))
  terminal_residue : ∀ u : ℕ, (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) →
    S ^ D₀ < (u : ℝ) → ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
      Int.fract (-(t : ℝ) / u) < (u : ℝ) ^ (-η)

/-- The weaker, directly consumable arithmetic data: only actual ceiling
residues are bounded. In particular a non-strict residue bound is sufficient. -/
structure ResidueData (DM D₀ η c r S loss : ℝ) (C M : ℕ) where
  indices : ℕ → Finset ℕ
  divisor : ℕ → ℕ → ℕ
  exceptional : ℕ → Finset ℕ
  indices_nonempty : ∀ j < depth DM η S, (indices j).Nonempty
  divisor_pos : ∀ j < depth DM η S, ∀ i ∈ indices j, 0 < divisor j i
  divisor_dvd : ∀ j < depth DM η S, ∀ i ∈ indices j, divisor j i ∣ M
  many_residues : ∀ j < depth DM η S, ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊,
    u ∉ exceptional j → cutoff DM η S (j + 1) < (u : ℝ) →
    contraction η S * ((indices j).card : ℝ) / loss ≤
      (((indices j).filter (fun i =>
        ((u * ⌈((factor DM η S C j * divisor j i : ℕ) : ℝ) / u⌉₊ -
          factor DM η S C j * divisor j i : ℕ) : ℝ) ≤ cutoff DM η S (j + 1))).card : ℝ)
  exception_bound : ∀ j < depth DM η S,
    ((exceptional j).card : ℝ) ≤ cutoff DM η S j *
      Real.exp (-c * ResidueLevels.scale S)
  moment_bound : ∀ j < depth DM η S, ∀ i ∈ indices j,
    (∑ h ∈ Finset.Icc 1 ⌊cutoff DM η S (j + 1)⌋₊,
      densityDivisorCount (cutoff DM η S j)
        (factor DM η S C j * divisor j i + h) ^ r) ≤
      cutoff DM η S (j + 1) * Real.exp (S ^ (1 / 4 : ℝ))
  terminal_residue : ∀ u : ℕ, (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) →
    S ^ D₀ < (u : ℝ) → ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
      ((u * ⌈(t : ℝ) / u⌉₊ - t : ℕ) : ℝ) ≤ (u : ℝ) ^ (1 - η)

/-- A normalized strict discrepancy conclusion implies the weaker ceiling
residue interface, without demanding a strict inequality from later consumers. -/
def NormalizedResidueData.toResidueData {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (H : NormalizedResidueData DM D₀ η c r S loss C M) (hS : 0 < S) :
    ResidueData DM D₀ η c r S loss C M := by
  refine {
    indices := H.indices
    divisor := H.divisor
    exceptional := H.exceptional
    indices_nonempty := H.indices_nonempty
    divisor_pos := H.divisor_pos
    divisor_dvd := H.divisor_dvd
    many_residues := ?_
    exception_bound := H.exception_bound
    moment_bound := H.moment_bound
    terminal_residue := ?_ }
  · intro j hj u hu huE hhigh
    apply (H.many_residues j hj u hu huE hhigh).trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hi, hsmall⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hi, ?_⟩
    have huX : (u : ℝ) ≤ cutoff DM η S j :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hu).2).trans
        (Nat.floor_le (ResidueLevels.level_pos _ _ _ j).le)
    have hsmall' := ceiling_residue_le_of_fract_lt (Finset.mem_Icc.mp hu).1
      (Real.exp_pos _).le huX hsmall
    simpa only [cutoff, contraction, ResidueLevels.level_succ] using hsmall'
  · intro u hu hSu
    obtain ⟨t, ht, htM, hsmall⟩ := H.terminal_residue u hu hSu
    have huR : (0 : ℝ) < u := (Real.rpow_pos_of_pos hS D₀).trans hSu
    have hu0 : 0 < u := by exact_mod_cast huR
    have hh := ceiling_residue_le_of_fract_lt hu0
      (Real.rpow_pos_of_pos huR (-η)).le (le_refl (u : ℝ)) hsmall
    have hp : (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (1 - η) := by
      calc
        (u : ℝ) ^ (-η) * u = (u : ℝ) ^ (-η) * (u : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (u : ℝ) ^ (-η + 1) := (Real.rpow_add huR _ _).symm
        _ = (u : ℝ) ^ (1 - η) := by congr 1; ring
    exact ⟨t, ht, htM, by simpa only [hp] using hh⟩

/-- Construct the exact raw family from ceiling residue information at the
canonical levels. This definition discharges every ceiling, divisibility,
terminal-expansion, and geometric-transition field. -/
def ResidueData.toFamily {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (H : ResidueData DM D₀ η c r S loss C M)
    (hDM : 1 < DM) (hD₀ : 1 ≤ D₀) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hS : 1 ≤ S) (hlog : 1 ≤ Real.log S) (hscale : 2 ≤ ResidueLevels.scale S)
    (hC : 0 < C) (hM : Real.exp S < (M : ℝ))
    (hbinary : 2 ^ TerminalDepth.binaryExponent D₀ S ∣ M)
    (hloss : 0 < loss)
    (hloss_bound : 1 + loss * Real.exp (S ^ (1 / 4 : ℝ) / r) ≤
      Real.exp (2 * S ^ (1 / 4 : ℝ))) :
    DensityResidueFamily S (ResidueLevels.scale S) (contraction η S) r c
      (depth DM η S) := by
  have hSpos : 0 < S := by linarith
  have hm : (0 : ℝ) < ResidueLevels.scale S := by exact_mod_cast (by omega :
    0 < ResidueLevels.scale S)
  have hmS : (ResidueLevels.scale S : ℝ) ≤ S :=
    ResidueLevels.scale_le_self hSpos.le hlog
  have hmA : (ResidueLevels.scale S : ℝ) ≤ (DM + 2) * S := by nlinarith
  have hα : 0 < 1 - η := by linarith
  have hα1 : 1 - η < 1 := by linarith
  have hMpos : 0 < M := by
    exact_mod_cast (Real.exp_pos S).trans hM
  have hfinal : cutoff DM η S (depth DM η S) ≤ Real.exp (ResidueLevels.scale S) :=
    (ResidueLevels.final_level_bounds hm hη hmA).2
  have hfinalS : cutoff DM η S (depth DM η S) ≤ Real.exp S :=
    hfinal.trans (Real.exp_le_exp.mpr hmS)
  have hfactor : factor DM η S C (depth DM η S) = 1 :=
    ResidueLevels.final_factor_one hm hη hmA hmS C
  have hterminal := TerminalAssembly.terminal_finite_expansions M
    (cutoff DM η S (depth DM η S)) D₀ (1 - η) S
    (ResidueLevels.level_pos _ _ _ _).le (hfinalS.trans_lt hM) hfinalS
    hD₀ hα hα1 hS hlog hbinary (by
      intro u hu hSu
      obtain ⟨t, ht, htM, hsmall⟩ := H.terminal_residue u (hu.trans hfinal) hSu
      have hu0 : 0 < u := by
        exact_mod_cast (Real.rpow_pos_of_pos hSpos D₀).trans hSu
      refine ⟨t, ⌈(t : ℝ) / u⌉₊, u * ⌈(t : ℝ) / u⌉₊ - t,
        ht, positive_ceiling_quotient ht hu0, htM, hsmall, ?_⟩
      exact (natural_ceil_residue_spec u t hu0).2.1.symm)
  refine {
    cutoff := cutoff DM η S
    exceptional := H.exceptional
    indices := H.indices
    residue := fun j i u =>
      u * ⌈((factor DM η S C j * H.divisor j i : ℕ) : ℝ) / u⌉₊ -
        factor DM η S C j * H.divisor j i
    denominator := M
    factor := factor DM η S C
    divisor := H.divisor
    quotient := fun j i u =>
      ⌈((factor DM η S C j * H.divisor j i : ℕ) : ℝ) / u⌉₊
    baseLength := ⌈TerminalAssembly.terminalCoefficient D₀ (1 - η) * Real.log S⌉₊
    loss := loss
    loss_pos := hloss
    loss_bound := hloss_bound
    cutoff_pos := fun j _ => ResidueLevels.level_pos _ _ _ j
    cutoff_step := fun j _ => ResidueLevels.level_succ _ _ _ j
    denominator_pos := hMpos
    factor_pos := fun j _ => ResidueLevels.factor_pos hC j
    factor_dvd := fun j _ => ResidueLevels.next_factor_dvd hm hη C j
    indices_nonempty := H.indices_nonempty
    divisor_pos := H.divisor_pos
    divisor_dvd := H.divisor_dvd
    quotient_pos := ?_
    residue_eq := ?_
    many_small_residues := H.many_residues
    exception_bound := H.exception_bound
    moment_bound := H.moment_bound
    terminal_expansions := ?_ }
  · intro j hj i hi u hu
    have hu0 : 0 < u := (Finset.mem_Icc.mp hu).1
    exact positive_ceiling_quotient
      (Nat.mul_pos (ResidueLevels.factor_pos hC j) (H.divisor_pos j hj i hi)) hu0
  · intro j hj i hi u hu
    exact (natural_ceil_residue_spec u
      (factor DM η S C j * H.divisor j i) (Finset.mem_Icc.mp hu).1).2.1.symm
  · intro u hu
    simpa only [hfactor, mul_one] using hterminal u hu

end GeometricDensity

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HighResidueDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The ordinary normalized exponential sum, defined also at modulus zero.
All residue conclusions below explicitly require a positive modulus. -/
def residueFourierAverage {Ω : Type*} [Fintype Ω]
    (A : Ω → ℕ) (u l : ℕ) : ℂ :=
  (∑ ω : Ω, Complex.exp
    (2 * Real.pi * Complex.I * (l * A ω : ℕ) / (u : ℂ))) /
      (Fintype.card Ω : ℂ)

/-- The Fourier exception set for the deterministic high levels. -/
def highResidueExceptions {Ω : Type*} [Fintype Ω]
    (U : Finset ℕ) (A : Ω → ℕ) (m : ℝ) : Finset ℕ := by
  classical
  exact U.filter (fun u => ∃ l ∈ Finset.Icc 1 ⌊Real.exp (m / 2500)⌋₊,
    Real.exp (-3 * m / 10000) < ‖residueFourierAverage A u l‖)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_HitCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

variable {α : Type*} [DecidableEq α]

/-- All words of a fixed length over a finite alphabet. -/
def sampleWords (P : Finset α) (t : ℕ) : Finset (Fin t → α) :=
  Fintype.piFinset (fun _ => P)

/-- Words having at least `k` coordinates in the distinguished set. -/
def hitWords (P H : Finset α) (t k : ℕ) : Finset (Fin t → α) :=
  (sampleWords P t).filter (fun f => k ≤ (Finset.univ.filter (fun i => f i ∈ H)).card)

/-- Words required to hit the distinguished set at each specified coordinate. -/
def hitCylinder (P H : Finset α) {t : ℕ} (T : Finset (Fin t)) : Finset (Fin t → α) :=
  Fintype.piFinset (fun i => if i ∈ T then H else P)

end Problem337.RandomProducts

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SmoothRankin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- The multiplicative weight occurring in divisor harmonic moments. -/
def divisorHarmonicWeight (r n : ℕ) : ℝ :=
  (n.divisors.card : ℝ) ^ r / (n : ℝ)

/-- A local Euler factor, in the indexing convenient for Rankin's trick. -/
def divisorEulerFactor (r p : ℕ) (β : ℝ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ r * ((p : ℝ) ^ (β - 1)) ^ j

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_IntermediatePrefixClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators Topology
open Filter

namespace Problem337.DivisorMoment

/-- Prime-factor prefix data defining one intermediate dyadic band. This does
not assume either a divisor-count estimate or a lower bound on the prefix. -/
def IntermediatePrefixWitness (n d p : ℕ) (Y v t : ℝ) : Prop :=
  d ∣ n ∧ (d : ℝ) ≤ Real.sqrt Y ∧ Real.sqrt Y < (d : ℝ) * p ∧ p.Prime ∧
  Real.log (p : ℝ) < v ^ (15 / 16 : ℝ) ∧
  t ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ 2 * t ∧
  (∀ q : ℕ, q.Prime → q ∣ d → q ≤ p) ∧
  (∀ q ∈ (n / d).primeFactorsList, p ≤ q)

end Problem337.DivisorMoment

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_LargePrefixClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The large-prime class, including integers already below the prefix cutoff.
The existential witnesses need not be chosen canonically. -/
def InLargePrefixClass (Z L : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) ≤ Z ∨ ∃ d p : ℕ, d ∣ n ∧ (d : ℝ) ≤ Z ∧ p.Prime ∧
    L ≤ Real.log (p : ℝ) ∧
    ∀ q : ℕ, q.Prime → q ∣ n / d → p ≤ q

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedGreedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337


/-- A finite trace of unreduced marked greedy steps. -/
inductive MarkedGreedySteps (m : ℕ) : ℕ → ℕ → List ℕ → ℕ → ℕ → Prop
  | nil (R q : ℕ) : MarkedGreedySteps m R q [] R q
  | cons (R q n c : ℕ) (L : List ℕ) (Rf qf : ℕ)
      (hn : 2 ≤ n) (hnm : n ≠ m) (hnq : n ≤ q + 1)
      (heq : n * R = q + c) (hcq : c < q) (hcR : c < 2 * R)
      (hord : n ≠ m + 1 → c < R)
      (tail : MarkedGreedySteps m c (n * q) L Rf qf) :
      MarkedGreedySteps m R q (n :: L) Rf qf

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkedReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators
open Filter

namespace Problem337

/-- The precise portion of the marked greedy-prefix output used by the final
construction.  The marker is not included in `p`; it is inserted afterwards. -/
def HasQuantitativeMarkedPrefix (m K : ℕ) : Prop :=
  ∃ p : Finset ℕ, ∃ q R : ℕ,
    0 < q ∧ R < 2 * m ∧ R * K ≤ q ∧ HasMarkedDivisorDensity m q ∧
    (∀ d ∈ p, 1 ≤ d) ∧ m ∉ p ∧
    ((1 : ℚ) / (m : ℚ) + ∑ d ∈ p, (1 : ℚ) / (d : ℚ)) +
      (R : ℚ) / (q : ℚ) = 1 ∧
    (∀ d ∈ insert m p, (R : ℚ) / (q : ℚ) < 1 / (d : ℚ)) ∧
    (p.card : ℝ) ≤ 3 + (Real.log (Real.log (2 * (m : ℝ) * (K : ℝ))) -
      Real.log (Real.log 2)) / Real.log 2

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkerOccurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

def pronic (j : ℕ) : ℕ := (j + 1) * (j + 2)

def pronicSet (m : ℕ) : Finset ℕ :=
  (Finset.range (m - 1)).image pronic

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MonotoneBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Good derivative indices in the integer cell labelled by `k`. -/
noncomputable def phaseGoodBlock (d : ℕ → ℝ) (N : ℕ) (β : ℝ) (k : ℤ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => (k : ℝ) + β ≤ d j ∧ d j ≤ (k : ℝ) + 1 - β)

noncomputable def nearIntegerIndices (d : ℕ → ℝ) (N : ℕ) (β : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun j => ∃ k : ℤ, |d j - (k : ℝ)| < β)

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_OddPrimorial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators
noncomputable section
namespace Problem337

/-- The product of the first `r` odd primes. -/
def oddPrimorial (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, Nat.nth Nat.Prime (i + 1)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PhaseExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Extend a finite phase by keeping its final increment constant. -/
def affineTailPhase (f : ℕ → ℝ) (N n : ℕ) : ℝ :=
  f 0 + ∑ j ∈ Finset.range n,
    (f (min j (N - 1) + 1) - f (min j (N - 1)))

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_PrimePool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- A prime pool in a fixed-width multiplicative interval. -/
def widePrimePool (x : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊64 * x⌋₊ \ Nat.primesLE ⌊x⌋₊

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomProductParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337.RandomProducts

/-- The short fresh-product length, with the constants used in the random
residue construction. -/
def freshLength (S V : ℝ) : ℕ := ⌊(3 / 4 : ℝ) * V / (100 * Real.log S)⌋₊

def blockLength (S : ℝ) : ℕ := ⌊S / Real.log S⌋₊

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomExposure

/-- Reindex all labelled samples into two free blocks and their exposed complement. -/
def splitSample {α β : Type*} [DecidableEq α] (A B : Finset α) (hAB : Disjoint A B) :
    (α → β) ≃ ((A → β) × (B → β) × ({i : α // i ∉ A ∧ i ∉ B} → β)) where
  toFun f := (fun i => f i, fun i => f i, fun i => f i)
  invFun f i := if ha : i ∈ A then f.1 ⟨i, ha⟩ else
    if hb : i ∈ B then f.2.1 ⟨i, hb⟩ else f.2.2 ⟨i, ha, hb⟩
  left_inv f := by
    funext i
    dsimp
    split_ifs <;> rfl
  right_inv f := by
    rcases f with ⟨a, b, c⟩
    apply Prod.ext
    · funext i
      simp [i.property]
    apply Prod.ext
    · funext i
      have hiA : (i : α) ∉ A := fun h => (Finset.disjoint_left.mp hAB) h i.property
      simp [hiA, i.property]
    · funext i
      simp [i.property.1, i.property.2]

@[simp] theorem splitSample_symm_left {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β) (i : A) :
    (splitSample A B hAB).symm (a, b, c) i = a i := by
  simp [splitSample, i.property]

@[simp] theorem splitSample_symm_right {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β) (i : B) :
    (splitSample A B hAB).symm (a, b, c) i = b i := by
  have hiA : (i : α) ∉ A := fun h => Finset.disjoint_left.mp hAB h i.property
  simp [splitSample, hiA, i.property]

@[simp] theorem splitSample_symm_exposed {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β)
    (i : {i : α // i ∉ A ∧ i ∉ B}) :
    (splitSample A B hAB).symm (a, b, c) i = c i := by
  simp [splitSample, i.property.1, i.property.2]

/-- The same exposure equivalence with exposed samples first, ready for conditional averages. -/
def splitSampleExposedFirst {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) :
    (α → β) ≃ (({i : α // i ∉ A ∧ i ∉ B} → β) × ((A → β) × (B → β))) :=
  (splitSample A B hAB).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _))

@[simp] theorem splitSampleExposedFirst_symm {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β) :
    (splitSampleExposedFirst A B hAB).symm (c, a, b) =
      (splitSample A B hAB).symm (a, b, c) := rfl

/-- The labelled coordinates selected by a Boolean word on a given coordinate set. -/
def selectedLabels {ι : Type*} [DecidableEq ι] (I : ι → Bool) (A : Finset ι) :
    Finset (ι × Bool) := A.image (fun i => (i, I i))

@[simp] theorem mem_selectedLabels {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) (A : Finset ι) (i : ι) (b : Bool) :
    (i, b) ∈ selectedLabels I A ↔ i ∈ A ∧ b = I i := by
  simp [selectedLabels, Prod.mk.injEq, and_left_comm, eq_comm]

@[simp] theorem selectedLabels_card {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) (A : Finset ι) : (selectedLabels I A).card = A.card := by
  apply Finset.card_image_of_injective
  intro i j h
  exact congrArg Prod.fst h

theorem selectedLabels_disjoint {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) {A B : Finset ι} (hAB : Disjoint A B) :
    Disjoint (selectedLabels I A) (selectedLabels I B) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i, b⟩ hiA hiB
  exact Finset.disjoint_left.mp hAB (mem_selectedLabels I A i b |>.mp hiA).1
    (mem_selectedLabels I B i b |>.mp hiB).1

/-- The other word uses none of the free labelled samples when the coordinates differ. -/
theorem other_word_exposed {ι : Type*} [DecidableEq ι]
    (I J : ι → Bool) (A : Finset ι) (hdiff : ∀ i ∈ A, I i ≠ J i) (i : ι) :
    (i, J i) ∉ selectedLabels I A := by
  rw [mem_selectedLabels]
  rintro ⟨hi, heq⟩
  exact hdiff i hi heq.symm

/-- The exposed label set. -/
abbrev ExposedLabel {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) (A B : Finset ι) :=
  {z : ι × Bool // z ∉ selectedLabels I A ∧ z ∉ selectedLabels I B}

/-- Every remaining coordinate of the first word is an exposed labelled sample. -/
def outsideSelectedLabel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Bool) (A B : Finset ι) (i : ↥(Finset.univ \ (A ∪ B))) : ExposedLabel I A B := by
  have hiAB : (i : ι) ∉ A ∪ B := (Finset.mem_sdiff.mp i.property).2
  have hi : (i : ι) ∉ A ∧ (i : ι) ∉ B := by
    exact ⟨fun h => hiAB (Finset.mem_union_left B h), fun h => hiAB (Finset.mem_union_right A h)⟩
  exact ⟨(i, I i), by simpa using hi.1, by simpa using hi.2⟩

/-- The first word's exposed factor, with an explicit product over the non-fresh coordinates. -/
def exposedFirstProduct {ι β M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (v : β → M) (I : ι → Bool) (A B : Finset ι) (c : ExposedLabel I A B → β) : M :=
  ∏ i : ↥(Finset.univ \ (A ∪ B)), v (c (outsideSelectedLabel I A B i))

/-- All coordinates of the second word remain exposed. -/
def exposedOtherProduct {ι β M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (v : β → M) (I J : ι → Bool) (A B : Finset ι)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (c : ExposedLabel I A B → β) : M :=
  ∏ i, v (c ⟨(i, J i), other_word_exposed I J A hA i, other_word_exposed I J B hB i⟩)

end Problem337.RandomExposure

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337.RandomProducts

def sampledProduct {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (I : Fin m → Bool) : ℕ :=
  ∏ j, (p (j, I j) : ℕ)

def sampledPhase {m : ℕ} {P : Finset ℕ} (u l : ℕ) [NeZero u]
    (p : (Fin m × Bool) → P) (I : Fin m → Bool) : ℂ :=
  ZMod.stdAddChar ((l * sampledProduct p I : ℕ) : ZMod u)

@[simp] theorem norm_sampledPhase {m : ℕ} {P : Finset ℕ} (u l : ℕ) [NeZero u]
    (p : (Fin m × Bool) → P) (I : Fin m → Bool) : ‖sampledPhase u l p I‖ = 1 := by
  exact AddChar.norm_apply _ _

open RandomExposure

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomCommonRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Total version of the normalized sampled character average. -/
def sampledMean {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u l : ℕ) : ℂ :=
  if hu : u = 0 then 0 else
    letI : NeZero u := ⟨hu⟩
    𝔼 I : Fin m → Bool, sampledPhase u l p I

@[simp] theorem sampledMean_eq {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u l : ℕ) [NeZero u] :
    sampledMean p u l = 𝔼 I : Fin m → Bool, sampledPhase u l p I := by
  simp [sampledMean, NeZero.ne u]

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RandomResidueRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The least nonnegative remainder used by numerator descent, for an actual
labelled prime sample and an actual Boolean choice. -/
def sampledRemainder {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (I : Fin m → Bool) : ℕ :=
  u * ⌈(sampledProduct p I : ℚ) / (u : ℚ)⌉₊ - sampledProduct p I


/-- The finite Fourier frequency window used at every scale. -/
def residueFrequencies (w : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊Real.exp (4 * w / 10000)⌋₊

end Problem337.RandomProducts

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RawDensityParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open Filter

namespace Problem337.RawDensityParameters

/-- The fixed denominator constant from the residue construction. -/
abbrev DM : ℝ := 204204
/-- The terminal binary cutoff exponent. -/
abbrev D₀ : ℝ := 100000
/-- The fixed geometric contraction rate. -/
abbrev η : ℝ := 1 / 10000
/-- The exponent in the exceptional-set estimate. -/
abbrev c : ℝ := 1 / 1000
/-- The logarithmic bound for the number of geometric levels. -/
abbrev K : ℝ := 3 * (DM + 2) / η
/-- A fixed moment exponent sufficient for the density recurrence. -/
abbrev r : ℝ := 8 * K
/-- The terminal expansion budget plus the backward descent budget. -/
abbrev L : ℝ := TerminalAssembly.terminalCoefficient D₀ (1 - η) + K + 1

end Problem337.RawDensityParameters

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ReciprocalPhaseUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- The terminal estimate needed at one fixed differencing order. -/
def ReciprocalTerminalPowerBound (k : ℕ) (C U : ℝ) : Prop :=
  ∀ Z : ℝ,
    U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
    |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
    ∀ L R : ℤ, U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
    ∀ hs : List ℤ, hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun x => Z / x) n)‖ ≤ C * U ^ ((4 : ℝ) / 5)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.ResidueConstruction

/-- The auxiliary denominator from one fixed block and a family of paired blocks. -/
def auxiliaryDenominator {m R : ℕ} (a : ℕ) (p : Fin m → ℕ)
    (q : Fin R → Fin m → Fin 2 → ℕ) : ℕ :=
  2 ^ a * (∏ j, p j) * ∏ i, ∏ j, ∏ e, q i j e

/-- The fixed block enumerates all subset products. -/
def subsetEntry {m : ℕ} (p : Fin m → ℕ) (I : Fin m → Fin 2) : ℕ :=
  ∏ j, p j ^ (I j).val

/-- A paired block selects exactly one entry from every pair. -/
def pairedEntry {m : ℕ} (q : Fin m → Fin 2 → ℕ) (I : Fin m → Fin 2) : ℕ :=
  ∏ j, q j (I j)

end Problem337.ResidueConstruction

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueRegimeSplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.GeometricDensity

/-- Combine the deterministic and sampled lists according to the level cutoff.
The index set is kept fixed, so repeated sampled products retain their full
multiplicity. The same choice also changes the auxiliary factor from `C` to `1`.
The shifted moment input is uniform over all positive divisors of the common
denominator; no moment assumption about the chosen list is added. -/
def residueData_of_two_lists
    {DM D₀ η c r S loss : ℝ} {C M : ℕ}
    (I : Finset ℕ) (hI : I.Nonempty) (t₀ t₁ : ℕ → ℕ)
    (hpos₀ : ∀ i ∈ I, 0 < t₀ i) (hpos₁ : ∀ i ∈ I, 0 < t₁ i)
    (hdvd₀ : ∀ i ∈ I, t₀ i ∣ M) (hdvd₁ : ∀ i ∈ I, t₁ i ∣ M)
    (E₀ E₁ : ℕ → Finset ℕ)
    (hcount₀ : ∀ j < depth DM η S, Real.exp S < cutoff DM η S j →
      ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E₀ j →
        cutoff DM η S (j + 1) < (u : ℝ) →
        contraction η S * (I.card : ℝ) / loss ≤
          ((I.filter (fun i => Int.fract (-((C * t₀ i : ℕ) : ℝ) / u) <
            contraction η S)).card : ℝ))
    (hcount₁ : ∀ j < depth DM η S, cutoff DM η S j ≤ Real.exp S →
      ∀ u ∈ Finset.Icc 1 ⌊cutoff DM η S j⌋₊, u ∉ E₁ j →
        cutoff DM η S (j + 1) < (u : ℝ) →
        contraction η S * (I.card : ℝ) / loss ≤
          ((I.filter (fun i => Int.fract (-(t₁ i : ℝ) / u) <
            contraction η S)).card : ℝ))
    (herror₀ : ∀ j < depth DM η S, Real.exp S < cutoff DM η S j →
      ((E₀ j).card : ℝ) ≤ cutoff DM η S j * Real.exp (-c * ResidueLevels.scale S))
    (herror₁ : ∀ j < depth DM η S, cutoff DM η S j ≤ Real.exp S →
      ((E₁ j).card : ℝ) ≤ cutoff DM η S j * Real.exp (-c * ResidueLevels.scale S))
    (hmoment : ∀ j < depth DM η S, ∀ t : ℕ, 0 < t → t ∣ M →
      (∑ h ∈ Finset.Icc 1 ⌊cutoff DM η S (j + 1)⌋₊,
        densityDivisorCount (cutoff DM η S j) (factor DM η S C j * t + h) ^ r) ≤
          cutoff DM η S (j + 1) * Real.exp (S ^ (1 / 4 : ℝ)))
    (hterminal : ∀ u : ℕ, (u : ℝ) ≤ Real.exp (ResidueLevels.scale S) →
      S ^ D₀ < (u : ℝ) → ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
        Int.fract (-(t : ℝ) / u) < (u : ℝ) ^ (-η)) :
    NormalizedResidueData DM D₀ η c r S loss C M := by
  classical
  let t : ℕ → ℕ → ℕ := fun j i =>
    if Real.exp S < cutoff DM η S j then t₀ i else t₁ i
  let E : ℕ → Finset ℕ := fun j =>
    if Real.exp S < cutoff DM η S j then E₀ j else E₁ j
  have hpos (j i : ℕ) (hi : i ∈ I) : 0 < t j i := by
    dsimp [t]
    split_ifs <;> first | exact hpos₀ i hi | exact hpos₁ i hi
  have hdvd (j i : ℕ) (hi : i ∈ I) : t j i ∣ M := by
    dsimp [t]
    split_ifs <;> first | exact hdvd₀ i hi | exact hdvd₁ i hi
  refine {
    indices := fun _ => I
    divisor := t
    exceptional := E
    indices_nonempty := fun _ _ => hI
    divisor_pos := fun j _ i hi => hpos j i hi
    divisor_dvd := fun j _ i hi => hdvd j i hi
    many_residues := ?_
    exception_bound := ?_
    moment_bound := fun j hj i hi => hmoment j hj (t j i) (hpos j i hi) (hdvd j i hi)
    terminal_residue := hterminal }
  · intro j hj u hu huE hunext
    by_cases hhigh : Real.exp S < cutoff DM η S j
    · have hnot : u ∉ E₀ j := by simpa only [E, ite_eq_left hhigh] using huE
      simpa only [t, ite_eq_left hhigh, factor, ResidueLevels.factor] using
        hcount₀ j hj hhigh u hu hnot hunext
    · have hnot : u ∉ E₁ j := by simpa only [E, ite_eq_right hhigh] using huE
      simpa only [t, ite_eq_right hhigh, factor, ResidueLevels.factor, one_mul] using
        hcount₁ j hj (le_of_not_gt hhigh) u hu hnot hunext
  · intro j hj
    by_cases hhigh : Real.exp S < cutoff DM η S j
    · simpa only [E, ite_eq_left hhigh] using herror₀ j hj hhigh
    · simpa only [E, ite_eq_right hhigh] using herror₁ j hj (le_of_not_gt hhigh)

end Problem337.GeometricDensity

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_SampledResidueDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Reindex Boolean product words by the two-element finite type used in the
auxiliary-denominator construction. No product values are identified. -/
def residueWordEquiv (m : ℕ) : (Fin m → Fin 2) ≃ (Fin m → Bool) :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) finTwoEquiv

/-- The same labelled samples, in the paired-block interface. -/
def residueSamplePairs {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) : Fin m → Fin 2 → ℕ :=
  fun j e => (f (j, finTwoEquiv e) : ℕ)

@[simp] theorem pairedEntry_residueSamplePairs {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) (I : Fin m → Fin 2) :
    ResidueConstruction.pairedEntry (residueSamplePairs f) I =
      sampledProduct f (residueWordEquiv m I) := by
  rfl

@[simp] theorem sampledProduct_residueWordEquiv_symm {m : ℕ} {P : Finset ℕ}
    (f : (Fin m × Bool) → P) (I : Fin m → Bool) :
    ResidueConstruction.pairedEntry (residueSamplePairs f)
      ((residueWordEquiv m).symm I) = sampledProduct f I := by
  rw [pairedEntry_residueSamplePairs, Equiv.apply_symm_apply]

end Problem337.RandomProducts

end

end OAI
end


