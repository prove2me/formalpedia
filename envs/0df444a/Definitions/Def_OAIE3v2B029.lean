-- Prove2me | Definitions.Def_OAIE3v2B029
-- name    : OAIE3v2B029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:03.340821+00:00
-- url     : https://prove2.me/theorems/0ed88002-31b8-443a-9e15-afc411cf8dfb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 30 of 311
-- statement:
--   Definitions bundle 30 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/PreparedEarlyStructuralPowerBudget.lean`, `Estimates/CopiedLayerSpace.lean`, `Estimates/FiniteMarkedFreezingCellBound.lean`, `Estimates/IntegralOrthogonalSection.lean`, `Estimates/LinearQuotientCoverAverage.lean`, `Estimates/McShaneEnvelope.lean`, `Estimates/NativeMarkedFreezingPhysicalData.lean`, `Estimates/NativeOptionTargetObservableRegularity.lean`, `Estimates/PositiveReconstruction.lean`, `Estimates/PositiveShiftRefilteredExpansionSpec.lean`, `Estimates/ProgressionPartitionComposition.lean`, `Estimates/SeparatedPositiveSum.lean`, `Estimates/UniformControlledNativeExternalNetsOfRecovery.lean`, `Fourier/FrequencyProjectionBudget.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/AllocatedGeometricInputBudget.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/BoxChartCutoff.lean`, `Geometry/BoxDetectionExponents.lean`, `Geometry/ChartCutoff.lean`, `Geometry/SortedLayerCoordinateEnumeration.lean`, `Geometry/SupportedBoxLipschitz.lean`, `Lattices/NormalizedLatticeSheet.lean`, `Lattices/PrimeCoordinateCells.lean`, `Lattices/ResidueBlockLongSideBudget.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Lattices/StandardLatticeCoordinates.lean`, `Linear/DeterminingMatrixDilation.lean`, `Linear/EpochEventRank.lean`, `Linear/NativeChartKernel.lean`, `Linear/NormalizedBasisBounds.lean`, `Linear/PreparedRoundedRank.lean`, `Linear/RankPreparationPotential.lean`, `Linear/TripleProductBasisBounds.lean`, `Nilpotent/SumNilmanifoldFactors.lean`, `Probability/AuxiliaryBoxLaws.lean`, `Probability/ObservedProductDensity.lean`, `Probability/ProbabilityIntegralThresholdPoint.lean`, `Sampling/FrozenPartitionScore.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FrozenPartitionScore
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem unit_weight_score_error {a W V ε : ℝ} (ha : |a| ≤ 1) (hclose : dist W V ≤ ε) :
    a * W ≤ a * V + ε := by
  have h : a * (W - V) ≤ ε := by
    calc
      _ ≤ |a * (W - V)| := le_abs_self _
      _ = |a| * |W - V| := abs_mul _ _
      _ ≤ 1 * ε := mul_le_mul ha (by simpa only [Real.dist_eq] using hclose) (abs_nonneg _) (by norm_num)
      _ = ε := one_mul _
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem progressionBlock_label_count (N q H : ℕ) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) ≤ N / H + q := by
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_add, Nat.mul_one]
  apply Nat.add_le_add_right
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm q H, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

theorem progressionBlock_label_count_mul (N q H : ℕ) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ N + q * H := by
  calc
    _ ≤ (N / H + q) * H := Nat.mul_le_mul_right H (progressionBlock_label_count N q H)
    _ = N / H * H + q * H := Nat.add_mul _ _ _
    _ ≤ N + q * H := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _

theorem progressionBlock_label_count_mul_le_twice {N q H : ℕ} (hfit : q * H ≤ N) :
    Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ 2 * N := by
  have h := progressionBlock_label_count_mul N q H
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem progressionBlock_short_side_bound {N q H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hfit : q * H ≤ N) {L : ℝ} (hL : 0 ≤ L) :
    (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * L / N ≤ 2 * L / H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_div_iff₀ hNr hHr).mpr
  have hc : (Fintype.card (Fin q × Fin (N / q / H + 1)) : ℝ) * H ≤ 2 * N := by
    exact_mod_cast progressionBlock_label_count_mul_le_twice hfit
  nlinarith [mul_le_mul_of_nonneg_right hc hL]

theorem boxBlock_short_side_budget {ι : Type*} [Fintype ι] (N H : ι → ℕ) (q : ℕ)
    (hN : ∀ i, 0 < N i) (hH : ∀ i, 0 < H i) (hfit : ∀ i, q * H i ≤ N i)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∑ i, (Fintype.card (Fin q × Fin (N i / q / H i + 1)) : ℝ) *
      (θ * H i / (2 * (Fintype.card ι + 1))) / N i) ≤ θ := by
  have hn : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  calc
    _ ≤ ∑ i, 2 * (θ * H i / (2 * (Fintype.card ι + 1))) / H i := by
      apply Finset.sum_le_sum
      intro i _
      exact progressionBlock_short_side_bound (hN i) (hH i) (hfit i) (by positivity)
    _ = ∑ _i : ι, θ / (Fintype.card ι + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have hHi : (H i : ℝ) ≠ 0 := by exact_mod_cast (hH i).ne'
      field_simp
    _ ≤ θ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hn).mpr
      nlinarith

theorem exists_box_block_mesh {ι : Type*} (N : ι → ℕ) (q : ℕ) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hlarge : ∀ i, 2 * (q : ℝ) ≤ ρ * N i) :
    ∃ H : ι → ℕ, (∀ i, 0 < H i) ∧ (∀ i, q * H i ≤ N i) ∧
      (∀ i, (q : ℝ) * H i ≤ ρ * N i) ∧
      (∀ i, ρ * N i / (2 * q) ≤ (H i : ℝ)) := by
  let H : ι → ℕ := fun i => ⌊ρ * N i / q⌋₊
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hx (i) : 2 ≤ ρ * N i / q := (le_div_iff₀ hqr).mpr (hlarge i)
  have hlo (i) : ρ * N i / q - 1 < (H i : ℝ) := Nat.sub_one_lt_floor _
  have hhi (i) : (H i : ℝ) ≤ ρ * N i / q := Nat.floor_le (by positivity)
  have hH (i) : 0 < H i := by
    have h : (0 : ℝ) < H i := by linarith [hlo i, hx i]
    exact_mod_cast h
  have hwidth (i) : (q : ℝ) * H i ≤ ρ * N i := by
    have h := (le_div_iff₀ hqr).mp (hhi i)
    simpa only [mul_comm] using h
  refine ⟨H, hH, ?_, hwidth, ?_⟩
  · intro i
    have h := (hwidth i).trans (mul_le_of_le_one_left (Nat.cast_nonneg (N i)) hρ1)
    exact_mod_cast h
  · intro i
    have heq : ρ * N i / (2 * q) = (ρ * N i / q) / 2 := by ring
    rw [heq]
    linarith [hlo i, hx i]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChartCutoff
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

noncomputable def chartCutoff {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ e.target then ψ (e.symm x) else 0

theorem chartCutoff_range {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (hψ : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (x : X) :
    0 ≤ chartCutoff e ψ x ∧ chartCutoff e ψ x ≤ 1 := by
  classical
  by_cases hx : x ∈ e.target
  · simpa only [chartCutoff, if_pos hx] using hψ (e.symm x)
  · simp only [chartCutoff, if_neg hx, le_refl, zero_le_one, and_self]

theorem lipschitz_chartCutoff {E X : Type*} [MetricSpace E] [MetricSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (A K δ : ℝ≥0) (hδ : 0 < δ)
    (hψ : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (hLip : LipschitzWith A ψ)
    (hInv : LipschitzOnWith K e.symm e.target)
    (hgap : ∀ x ∈ e.target, ψ (e.symm x) ≠ 0 → ∀ y ∉ e.target, (δ : ℝ) ≤ dist x y) :
    LipschitzWith (A * K + 1 / δ) (chartCutoff e ψ) := by
  classical
  have hδ' : (0 : ℝ) < δ := hδ
  have hcross (x) (hx : x ∈ e.target) (y) (hy : y ∉ e.target) :
      dist (ψ (e.symm x)) 0 ≤ ((A * K + 1 / δ : ℝ≥0) : ℝ) * dist x y := by
    by_cases hz : ψ (e.symm x) = 0
    · rw [hz, dist_self]
      positivity
    · have hd := hgap x hx hz y hy
      calc
        _ = ψ (e.symm x) := by rw [Real.dist_eq, sub_zero, abs_of_nonneg (hψ _).1]
        _ ≤ 1 := (hψ _).2
        _ ≤ (1 / (δ : ℝ)) * dist x y := by
          have hd' := (div_le_div_iff_of_pos_right hδ').mpr hd
          simpa only [div_self (ne_of_gt hδ'), one_div_mul_eq_div] using hd'
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right ?_ dist_nonneg
          simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one]
          exact le_add_of_nonneg_left (mul_nonneg A.coe_nonneg K.coe_nonneg)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ e.target <;> by_cases hy : y ∈ e.target
  · simp only [chartCutoff, if_pos hx, if_pos hy]
    calc
      _ ≤ (A : ℝ) * dist (e.symm x) (e.symm y) := hLip.dist_le_mul _ _
      _ ≤ (A : ℝ) * ((K : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left (hInv.dist_le_mul x hx y hy) A.coe_nonneg
      _ ≤ _ := by
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one]
        nlinarith [mul_nonneg (one_div_nonneg.mpr δ.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · simpa only [chartCutoff, if_pos hx, if_neg hy] using hcross x hx y hy
  · simpa only [chartCutoff, if_neg hx, if_pos hy, dist_comm] using hcross y hy x hx
  · simp only [chartCutoff, if_neg hx, if_neg hy, dist_self]
    positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxChartCutoff
namespace OAI

section

namespace Erdos3

open _root_.Set

theorem closedBox_subset_chart_source {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r}) :
    Metric.closedBall 0 (3 * r / 4) ⊆ φ.source := by
  intro v hv
  rw [hsource]
  intro i
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  have hi := (norm_le_pi_norm v i).trans hv
  rw [Real.norm_eq_abs] at hi
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxDetectionExponents
namespace OAI

section

namespace Erdos3

def boxModeBudget (a : ℕ) (p : ℝ) : ℝ := p + (p + 1 + a) ^ a + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

def integerResidueLabel (d : ℕ) (hd : 0 < d) (x : ℤ) : Fin d :=
  ⟨(x % (d : ℤ)).toNat, by
    have hlo := Int.emod_nonneg x (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
    have hhi := Int.emod_lt_of_pos x (show (0 : ℤ) < d by exact_mod_cast hd)
    omega⟩

theorem integerResidueLabel_val (d : ℕ) (hd : 0 < d) (x : ℤ) :
    ((integerResidueLabel d hd x).val : ℤ) = x % (d : ℤ) := by
  have hlo := Int.emod_nonneg x (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
  exact Int.toNat_of_nonneg hlo

theorem integerResidueLabel_eq_iff (d : ℕ) (hd : 0 < d) (x : ℤ) (v : Fin d) :
    integerResidueLabel d hd x = v ↔ x ≡ (v.val : ℤ) [ZMOD (d : ℤ)] := by
  have hv : (v.val : ℤ) % (d : ℤ) = v.val := Int.emod_eq_of_lt
    (Int.natCast_nonneg _) (by exact_mod_cast v.isLt)
  have hx := integerResidueLabel_val d hd x
  rw [Int.ModEq, hv, Fin.ext_iff]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedPositiveSum
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem separated_tsum_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (f : ι → X → ℝ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hpos : ∀ i x, 0 ≤ f i x)
    (hsep : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith K (fun x => ∑' i, f i x) := by
  have hsingle (x : X) (i : ι) (hi : f i x ≠ 0) : (∑' j, f j x) = f i x := by
    apply tsum_eq_single i
    intro j hji
    by_contra hj
    exact hji (hsep x j i hj hi)
  have hdom (x : X) (i : ι) : f i x ≤ ∑' j, f j x := by
    by_cases hi : f i x = 0
    · rw [hi]
      exact tsum_nonneg (fun j => hpos j x)
    · rw [hsingle x i hi]
  have hsub (x y : X) : (∑' i, f i x) - (∑' i, f i y) ≤ K * dist x y := by
    by_cases hx : ∃ i, f i x ≠ 0
    · obtain ⟨i, hi⟩ := hx
      rw [hsingle x i hi]
      have h := (le_abs_self (f i x - f i y)).trans ((hf i).dist_le_mul x y)
      linarith [hdom y i]
    · have hz : ∀ i, f i x = 0 := fun i => not_ne_iff.mp (fun hi => hx ⟨i, hi⟩)
      simp only [hz, tsum_zero, zero_sub]
      exact le_trans (neg_nonpos.mpr (tsum_nonneg (fun i => hpos i y)))
        (mul_nonneg K.coe_nonneg dist_nonneg)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := hsub x y
  have hyx := hsub y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SupportedBoxLipschitz
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem lipschitzWith_of_unit_range_support_box {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) (R L : ℝ≥0)
    (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1)
    (hsupport : ∀ x, f x ≠ 0 → ∀ i, |x i| ≤ R)
    (hlip : LipschitzOnWith L f {x | ∀ i, |x i| ≤ (R : ℝ) + 1}) :
    LipschitzWith (max 1 L) f := by
  have hL : (L : ℝ) ≤ (max 1 L : ℝ≥0) := by exact_mod_cast (le_max_right 1 L)
  have hnear (x y : I → ℝ) (hx : f x ≠ 0) (hxy : dist x y < 1) :
      dist (f x) (f y) ≤ L * dist x y := by
    have hxR : ∀ i, |x i| ≤ (R : ℝ) + 1 := fun i => (hsupport x hx i).trans (by linarith)
    have hyR : ∀ i, |y i| ≤ (R : ℝ) + 1 := by
      intro i
      have hi : |y i - x i| ≤ dist x y := by
        calc
          |y i - x i| ≤ dist y x := by simpa only [Real.dist_eq] using dist_le_pi_dist y x i
          _ = dist x y := dist_comm y x
      calc
        |y i| = |(y i - x i) + x i| := by ring_nf
        _ ≤ |y i - x i| + |x i| := abs_add_le _ _
        _ ≤ (R : ℝ) + 1 := by linarith [hsupport x hx i]
    exact hlip.dist_le_mul x hxR y hyR
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hxy : dist x y < 1
  · by_cases hx : f x = 0
    · by_cases hy : f y = 0
      · rw [hx, hy, dist_self]
        positivity
      · have h := hnear y x hy (by simpa only [dist_comm] using hxy)
        rw [dist_comm (f y) (f x), dist_comm y x] at h
        exact h.trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
    · exact (hnear x y hx hxy).trans (mul_le_mul_of_nonneg_right hL dist_nonneg)
  · have hdist : dist (f x) (f y) ≤ 1 := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hzero x, hzero y, hone x, hone y]
    have hlarge : (1 : ℝ) ≤ dist x y := le_of_not_gt hxy
    have hmax : (1 : ℝ) ≤ (max 1 L : ℝ≥0) := by exact_mod_cast (le_max_left 1 L)
    exact hdist.trans (hlarge.trans (by nlinarith [dist_nonneg (x := x) (y := y)]))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeChartKernel
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem chartKernelScaling_lipschitz (d B : ℕ) :
    LipschitzWith (B : ℝ≥0) (fun x : Fin d → ℝ => (B : ℝ) • x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) B), NNReal.coe_natCast]
  exact le_rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TripleProductBasisBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*}
  [Fintype ι]
  {L : ι → Type*}
  [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ}
  {d : ι → ℕ}

noncomputable def productBasisWeight (weight : ∀ i, Fin (d i) → ℕ)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) : ℕ :=
  let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
  weight z.1 z.2

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.McShaneEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def mcShaneEnvelope (f : X → ℝ) (y : Y) : ℝ :=
  ⨅ x, f x + L * dist y (φ x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveReconstruction
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def positiveClip (z : ℂ) : ℂ := (max 0 (min 1 z.re) : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

def restrictedFrequencySpan (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    Submodule ℚ (Module.Dual ℚ P) :=
  Submodule.span ℚ ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})

end Erdos3

end

section

namespace Erdos3

open Module

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V]

theorem exists_restricted_frequency_basis [FiniteDimensional ℚ V] (P : Submodule ℚ V)
    (eta : J → V →ₗ[ℚ] ℚ) (js : List J) :
    ∃ m : ℕ, m ≤ finrank ℚ P ∧ ∃ indices : Fin m → J,
      (∀ i, indices i ∈ js) ∧
      LinearIndependent ℚ (fun i => (eta (indices i)).comp P.subtype) ∧
      Submodule.span ℚ (Set.range (fun i => (eta (indices i)).comp P.subtype)) =
        restrictedFrequencySpan P eta js := by
  classical
  let W := restrictedFrequencySpan P eta js
  obtain ⟨u, hu, hspan, hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    ((fun j => (eta j).comp P.subtype) '' {j | j ∈ js})
  have hex (i : Fin (finrank ℚ W)) :
      ∃ j, j ∈ js ∧ (eta j).comp P.subtype = u i := hu i
  choose indices hindices heq using hex
  have hfun : (fun i => (eta (indices i)).comp P.subtype) = u := funext heq
  refine ⟨finrank ℚ W, ?_, indices, hindices, ?_, ?_⟩
  · have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    omega
  · rw [hfun]
    exact hlin
  · rw [hfun]
    exact hspan

theorem restrictedFrequencySpan_finRange (P : Submodule ℚ V) {m : ℕ}
    (eta : Fin m → V →ₗ[ℚ] ℚ) :
    restrictedFrequencySpan P eta (List.finRange m) =
      Submodule.span ℚ (Set.range (fun i => (eta i).comp P.subtype)) := by
  unfold restrictedFrequencySpan
  congr 1
  ext x
  simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NormalizedBasisBounds
namespace OAI

section

namespace Erdos3

open Module MeasureTheory
open scoped BigOperators

variable {I E : Type*} [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem covolume_basis_eq_orthonormal_det [DecidableEq I]
    (o : OrthonormalBasis I ℝ E) (b : Basis I ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
  classical
  have hvolume : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_def]
    have hfd : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis, hvolume, mul_one]

theorem covolume_basis_scale (o : OrthonormalBasis I ℝ E) (b c : Basis I ℝ E)
    (t : I → ℝ) (ht : ∀ i, 0 ≤ t i) (hc : ∀ i, c i = t i • b i) :
    ZLattice.covolume (Submodule.span ℤ (Set.range c)) =
      (∏ i, t i) * ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  classical
  rw [covolume_basis_eq_orthonormal_det o c, covolume_basis_eq_orthonormal_det o b]
  rw [show (c : I → E) = (fun i => t i • b i) from funext hc,
    AlternatingMap.map_smul_univ, smul_eq_mul, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg (fun i _ => ht i))]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem orthonormal_basis_coordinate_abs_le (o : OrthonormalBasis I ℝ E) (x : E) (i : I) :
    |o.toBasis.equivFun x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le (o.repr x) i
  change |o.repr x i| ≤ ‖x‖
  simpa only [Real.norm_eq_abs, LinearIsometryEquiv.norm_map] using h

end Erdos3

end

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators Matrix

theorem basis_synthesis_norm_le {E : Type*} {n : ℕ}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis (Fin n) ℝ E) {H : ℝ} (hb : ∀ i, ‖b i‖ ≤ H) (x : Fin n → ℝ) :
    ‖b.equivFun.symm x‖ ≤ (n : ℝ) * H * ‖x‖ := by
  rw [Basis.equivFun_symm_apply]
  calc
    _ ≤ ∑ i, ‖x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * H := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm x i) (hb i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

namespace VectorPolynomial

def appendRankCutRow {ι ρ : Type*} (A : Matrix ρ ι ℚ) (a : ι → ℤ) :
    Matrix (Option ρ) ι ℚ :=
  Matrix.of (fun r i => r.elim (a i : ℚ) (fun r => A r i))

open scoped TensorProduct

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet
namespace OAI

section

namespace Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanDualLattice (Λ : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ

theorem mem_euclideanDualLattice (Λ : Submodule ℤ E) (ξ : E) :
    ξ ∈ euclideanDualLattice Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ) := by
  simp only [euclideanDualLattice, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, innerₗ_apply_apply]
  exact forall_congr' (fun _ => forall_congr' (fun _ => exists_congr (fun _ => eq_comm)))

theorem realInner_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

variable [FiniteDimensional ℝ E]

theorem euclideanDualLattice_eq_span_dualBasis (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate
        ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ))) := by
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E) realInner_nondegenerate
    ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, Module.Basis.ofZLatticeBasis_span] using h

instance euclideanDualLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : DiscreteTopology (euclideanDualLattice Λ) := by
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  infer_instance

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IntegralOrthogonalSection
namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem ker_basis_inner_eq_orthogonal {I : Type*} [Fintype I]
    (W : Submodule ℝ E) (b : Basis I ℝ W) :
    LinearMap.ker (LinearMap.pi (fun i => innerₗ E (b i).val)) = Wᗮ := by
  have hspan : span ℝ (Set.range (fun i => (b i : E))) = W := by
    change span ℝ (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  ext x
  constructor
  · intro hx
    have hz : (LinearMap.pi (fun i => innerₗ E (b i).val)) x = 0 := hx
    have hW : W ≤ LinearMap.ker (innerₗ E x) := by
      rw [← hspan]
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      change inner ℝ x (b i : E) = 0
      rw [real_inner_comm]
      exact congrFun hz i
    exact (W.mem_orthogonal' x).mpr (fun y hy => hW hy)
  · intro hx
    apply LinearMap.mem_ker.mpr
    ext i
    exact Submodule.inner_right_of_mem_orthogonal (b i).property hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

noncomputable def probabilityAddHaar (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : Measure G :=
  Measure.addHaarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance probabilityAddHaar_probability (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : IsProbabilityMeasure (probabilityAddHaar G) where
  measure_univ := Measure.addHaarMeasure_self

instance probabilityAddHaar_invariant (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [T2Space G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : (probabilityAddHaar G).IsAddLeftInvariant :=
  inferInstanceAs (Measure.addHaarMeasure _).IsAddLeftInvariant

theorem compact_quotient_of_integral_basis {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (Γ : AddSubgroup E) (b : Basis ι ℝ E) (hb : ∀ i, b i ∈ Γ) : CompactSpace (E ⧸ Γ) := by
  let L := Submodule.span ℤ (Set.range b)
  have hin : L ≤ Γ.toIntSubmodule := Submodule.span_le.mpr (by
    rintro _ ⟨i, rfl⟩
    exact hb i)
  have hc := IsZLattice.isCompact_range_of_periodic L (QuotientAddGroup.mk' Γ)
    (QuotientAddGroup.isQuotientMap_mk Γ).continuous (by
      intro x z hz
      rw [map_add]
      have hzero : QuotientAddGroup.mk' Γ z = 0 :=
        (QuotientAddGroup.eq_zero_iff z).mpr (hin hz)
      rw [hzero, add_zero])
  rw [Set.range_eq_univ.mpr (QuotientAddGroup.mk'_surjective Γ)] at hc
  exact ⟨hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StandardLatticeCoordinates
namespace OAI

section

namespace Erdos3

open Module Submodule

variable {J : Type*} [Fintype J]

noncomputable def projectedIntegerGenerator (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) : Wᗮ :=
  Wᗮ.orthogonalProjectionOnto (EuclideanSpace.basisFun J ℝ i)

theorem projectedIntegerGenerator_norm_le (W : Submodule ℝ (EuclideanSpace ℝ J)) (i : J) :
    ‖projectedIntegerGenerator W i‖ ≤ 1 := by
  have h := Wᗮ.norm_orthogonalProjectionOnto_apply_le (EuclideanSpace.basisFun J ℝ i)
  simpa only [projectedIntegerGenerator, OrthonormalBasis.norm_eq_one] using h

theorem projectedIntegerGenerator_span (W : Submodule ℝ (EuclideanSpace ℝ J)) :
    span ℝ (Set.range (projectedIntegerGenerator W)) = ⊤ := by
  change span ℝ (Set.range (Wᗮ.orthogonalProjectionOnto.toLinearMap ∘
    (EuclideanSpace.basisFun J ℝ).toBasis)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top]
  apply LinearMap.range_eq_top.mpr
  intro w
  refine ⟨w.val, ?_⟩
  apply Subtype.ext
  exact Wᗮ.starProjection_eq_self_iff.mpr w.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def ProductDependsOn {I : Type*} {X : I → Type*} (S : Finset I)
    (f : (∀ i, X i) → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformControlledNativeExternalNetsOfRecovery
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {X Y : Type*} [Nonempty X] [PseudoMetricSpace Y]
  (φ : X → Y) (L : ℝ≥0)

noncomputable def positiveImageExtension (f : X → ℂ) (y : Y) : ℂ :=
  positiveClip (mcShaneEnvelope φ L (fun x => (f x).re) y)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X Y Z : Type*} [Nonempty X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  (φ : X → Y × Z) (L : ℝ≥0)

noncomputable def positiveImageSlice (f : X → ℂ) (z : Z) (y : Y) : ℂ :=
  positiveImageExtension φ L f (y, z)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AuxiliaryBoxLaws
namespace OAI

section

namespace Erdos3

theorem refinedResidue_implies_base (M J : ℕ) (u w : ℤ)
    (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) (hx : x ≡ w [ZMOD (M * J : ℕ)]) :
    x ≡ u [ZMOD (M : ℤ)] :=
  (Int.ModEq.of_dvd (by exact_mod_cast dvd_mul_right M J) hx).trans hw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyProjectionBudget
namespace OAI

section

namespace Erdos3

theorem frequency_projection_error_bound {p v M : ℝ} (hp : 0 ≤ p)
    (hM : M ≤ Real.exp v) :
    2 * Real.exp p * Real.exp (-(2 * p + 8)) + M * Real.exp (-(p + v + 8)) ≤
      Real.exp (-p) / 2 := by
  have parameterNonneg := hp
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hinv : Real.exp (-8 : ℝ) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) h8
  have hfirst : 2 * Real.exp p * Real.exp (-(2 * p + 8)) =
      2 * Real.exp (-p) * Real.exp (-8) := by
    rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hsecond : Real.exp v * Real.exp (-(p + v + 8)) = Real.exp (-p) * Real.exp (-8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hbound := mul_le_mul_of_nonneg_right hM (Real.exp_nonneg (-(p + v + 8)))
  rw [hsecond] at hbound
  rw [hfirst]
  have hsmall := mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg (-p))
  linarith [parameterNonneg, Real.exp_pos (-p)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ProbabilityIntegralThresholdPoint
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {Λ : Type*} [MeasurableSpace Λ]

theorem probabilityIntegralThresholdPoint (μ : Measure Λ) [IsProbabilityMeasure μ]
    {m : Λ → ℝ} (hm : Integrable m μ) {c : ℝ} (hc : c ≤ ∫ l, m l ∂μ) :
    ∃ l, c ≤ m l := by
  obtain ⟨l, hl⟩ := exists_integral_le hm
  exact ⟨l, hc.trans hl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SumNilmanifoldFactors
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

def sumLieSpace {ι κ : Type*} (L : ι → Type u) (M : κ → Type u) : ι ⊕ κ → Type u
  | .inl i => L i
  | .inr j => M j

instance sumLieRing {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)] (k : ι ⊕ κ) : LieRing (sumLieSpace L M k) := by
  cases k <;> dsimp [sumLieSpace] <;> infer_instance

instance sumLieAlgebra {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] (k : ι ⊕ κ) :
    LieAlgebra ℚ (sumLieSpace L M k) := by
  cases k <;> dsimp [sumLieSpace] <;> infer_instance

instance sumRealificationTopology {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] (k : ι ⊕ κ) :
    TopologicalSpace (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : TopologicalSpace (ℝ ⊗[ℚ] M j))

instance sumRealificationTopologicalAddGroup {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : IsTopologicalAddGroup (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : IsTopologicalAddGroup (ℝ ⊗[ℚ] M j))

instance sumRealificationContinuousSMul {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : ContinuousSMul ℝ (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : ContinuousSMul ℝ (ℝ ⊗[ℚ] M j))

instance sumRealificationT2Space {ι κ : Type*} {L : ι → Type u} {M : κ → Type u}
    [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
    [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)]
    [∀ i, T2Space (ℝ ⊗[ℚ] L i)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
    (k : ι ⊕ κ) : T2Space (ℝ ⊗[ℚ] sumLieSpace L M k) := by
  cases k with
  | inl i => exact (inferInstance : T2Space (ℝ ⊗[ℚ] L i))
  | inr j => exact (inferInstance : T2Space (ℝ ⊗[ℚ] M j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
namespace OAI

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold
open scoped TensorProduct

def productExpansionBudget (p : ℝ) : ℝ := (2 * p + 4) ^ 2 + p + 2

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedGeometricInputBudget
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

def allocatedUniformChartLog {A : Type*} [Semiring A] (p : A) : A := 20 * (p + 1) ^ 3

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CopiedLayerSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

def copiedLayerSpace {J K : Type*} (W : Submodule ℝ (J → ℝ)) (V : Submodule ℝ (K → ℝ)) :
    Submodule ℝ (J ⊕ K → ℝ) where
  carrier := {x | (fun j => x (.inl j)) ∈ W ∧ (fun k => x (.inr k)) ∈ V}
  zero_mem' := ⟨W.zero_mem, V.zero_mem⟩
  add_mem' hx hy := ⟨W.add_mem hx.1 hy.1, V.add_mem hx.2 hy.2⟩
  smul_mem' r _ hx := ⟨W.smul_mem r hx.1, V.smul_mem r hx.2⟩

def copiedLayerMatrix {J K C : Type*} (B : Matrix J C ℚ) (e : K → ℚ) :
    Matrix (J ⊕ K) (Option C) ℚ :=
  Matrix.of (fun j c => match j, c with
    | .inl j, .some c => B j c
    | .inr k, .none => e k
    | _, _ => 0)

def copiedLayerRows {J K V : Type*} (A : Matrix V J ℚ) : Matrix V (J ⊕ K) ℚ :=
  Matrix.of (fun r j => Sum.elim (A r) (fun _ => 0) j)

theorem copiedLayerMatrix_real_mulVec {J K C : Type*} [Fintype C]
    (B : Matrix J C ℚ) (e : K → ℚ) (z : Option C → ℝ) :
    Matrix.of (fun j c => (copiedLayerMatrix B e j c : ℝ)) *ᵥ z =
      Sum.elim (Matrix.of (fun j c => (B j c : ℝ)) *ᵥ (fun c => z (some c)))
        (fun k => z none * (e k : ℝ)) := by
  classical
  ext j
  cases j <;> simp [Matrix.mulVec, dotProduct, copiedLayerMatrix, Fintype.sum_option, mul_comm]

theorem copiedLayerRows_real_mulVec {J K V : Type*} [Fintype J] [Fintype K]
    (A : Matrix V J ℚ) (x : J ⊕ K → ℝ) :
    Matrix.of (fun r j => (copiedLayerRows A r j : ℝ)) *ᵥ x =
      Matrix.of (fun r j => (A r j : ℝ)) *ᵥ (fun j => x (.inl j)) := by
  classical
  ext r
  simp [Matrix.mulVec, dotProduct, copiedLayerRows, Fintype.sum_sum_type]

def copyLeft {J K : Type*} : (J → ℝ) →ₗ[ℝ] (J ⊕ K → ℝ) where
  toFun v := Sum.elim v 0
  map_add' _ _ := by ext j; cases j <;> simp
  map_smul' _ _ := by ext j; cases j <;> simp

def copyRight {J K : Type*} : (K → ℝ) →ₗ[ℝ] (J ⊕ K → ℝ) where
  toFun v := Sum.elim 0 v
  map_add' _ _ := by ext j; cases j <;> simp
  map_smul' _ _ := by ext j; cases j <;> simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPotential
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def layerRankPotential {s : ℕ} (d : Fin s → ℕ) : ℕ :=
  ∑ i, (i.val + 1) * d i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

def preparationCoordinateCap (s D T : ℕ) : ℕ := D * (T + 1) ^ s + D + T + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMarkedFreezingCellBound
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module
open scoped TensorProduct NNReal

theorem subdivisionCount_le_function_card {σ : Type*} [Fintype σ] [DecidableEq σ]
    [Nonempty σ] (Q : ℕ) : Q + 1 ≤ Fintype.card (σ → Fin (Q + 1)) := by
  classical
  have hinj : Function.Injective (fun a : Fin (Q + 1) => fun _ : σ => a) := by
    intro a b hab
    exact congrFun hab (Classical.choice inferInstance)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBlockLongSideBudget
namespace OAI

section

namespace Erdos3

theorem residueBlock_long_side_budget {θ : ℝ} {N q Q H : ℕ}
    (hθ : 0 < θ) (hN : 0 < N) (hq : 0 < q) (hQ : 0 < Q)
    (hH : (N : ℝ) / (2 * q * Q) ≤ H) (n : ℕ) :
    θ * N / (4 * q * Q * (n + 1 : ℝ)) ≤ θ * H / (2 * (n + 1 : ℝ)) ∧
      0 < θ * H / (2 * (n + 1 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHr : (0 : ℝ) < H := (by positivity : 0 < (N : ℝ) / (2 * q * Q)).trans_le hH
  refine ⟨?_, by positivity⟩
  calc
    _ = (θ / (2 * (n + 1 : ℝ))) * ((N : ℝ) / (2 * q * Q)) := by
      field_simp
      ring
    _ ≤ (θ / (2 * (n + 1 : ℝ))) * H :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedFreezingPhysicalData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

def nativeMarkedFreezingPhysicalParameter (p : ℝ) (C : ℕ) : ℝ :=
  (p + 3) ^ 36 + (p + C) ^ C

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionTargetObservableRegularity
namespace OAI

section

universe u v w₀ w₁ w₂

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct NNReal

def nativeOptionTargetObservableBudget (p : ℝ) : ℝ :=
  (p + 3) ^ 2 + 2 + 2 * ((p + 3) ^ 2 + 4) ^ 2

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SortedLayerCoordinateEnumeration
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {m : ℕ} (E : Fin m → Type) [∀ j, Fintype (E j)]

noncomputable def sortedLayerCoordinateEquiv :
    Fin (Fintype.card (Σ j, E j)) ≃ (Σ j, E j) :=
  (Tuple.sort (fun i : Fin (Fintype.card (Σ j, E j)) =>
    ((Fintype.equivFin (Σ j, E j)).symm i).1.val + 1)).trans
    (Fintype.equivFin (Σ j, E j)).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EpochEventRank
namespace OAI

section

namespace Erdos3

def epochStackRank (d : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r * (d + 1) ^ rs.length + epochStackRank d rs

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeCoordinateCells
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def periodPrimeCoordinates {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (M : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => prime i ∣ M)

@[simp] theorem mem_periodPrimeCoordinates {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (M : ℕ) (i : ι) :
    i ∈ periodPrimeCoordinates prime M ↔ prime i ∣ M := by
  classical
  simp [periodPrimeCoordinates]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DeterminingMatrixDilation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d m : ℕ}

def dilatedIntegerMatrix (q : ℕ) (M : Fin m → Fin d → ℤ) : Fin m → Fin d → ℤ :=
  fun i j => (q : ℤ) * M i j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedRoundedRank
namespace OAI

section

namespace Erdos3

noncomputable def preparedRoundedRank (p : ℝ) (e : ℕ) : ℕ :=
  ⌈Real.exp ((p + 2)^e)⌉₊

end Erdos3

end

end OAI
end


