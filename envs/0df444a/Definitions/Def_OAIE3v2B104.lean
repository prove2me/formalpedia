-- Prove2me | Definitions.Def_OAIE3v2B104
-- name    : OAIE3v2B104
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:28:54.788025+00:00
-- url     : https://prove2.me/theorems/75e4b727-c729-480d-9072-57b4565da851
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 106 of 311
-- statement:
--   Definitions bundle 106 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B091`, `OAIE3v2B092` of this split.
--
--   Modules: `Dynamics/ReconstructionBudget.lean`, `Estimates/AdaptedTranslation.lean`, `Estimates/CyclicRelativeChang.lean`, `Estimates/DilationCost.lean`, `Estimates/FiniteGoodPartTransfer.lean`, `Estimates/HorizontalAmbientQuotient.lean`, `Estimates/LocalizedSiftingAlmostPeriods.lean`, `Estimates/ObservedSourceEquivalence.lean`, `Estimates/OneSiteWeightIdentity.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PinnedSectionMeans.lean`, `Estimates/PositiveNormalizationError.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealifiedReconstruction.lean`, `Estimates/ScalarDominatedSlack.lean`, `Estimates/SquareGradedRelative.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `Estimates/UniformCommutingCircleDecomposition.lean`, `FixedDensity/GeneratorCells.lean`, `FixedDensity/OrderedBoundaryPartition.lean`, `FixedDensity/OrderedRemoval.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/BohrTorusApproximation.lean`, `Fourier/LocalBohrAlmostPeriodsRelative.lean`, `Fourier/LocalSpectrumBudget.lean`, `Fourier/TranslatedBohrDifference.lean`, `Lattices/AffineOneSiteNormalizedLaw.lean`, `Lattices/AlgebraicMajorWeightedAffineTopPullback.lean`, `Lattices/LayerSamplingRankAffine.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/FiniteCenteredKernel.lean`, `Linear/HomogeneousLieSpan.lean`, `Linear/MarkedLieSpan.lean`, `Nilpotent/BCHDenominatorBudget.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/DegreeRankBCH.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Probability/CylinderJointMass.lean`, `Probability/IntervalDivisorProbability.lean`, `Probability/ObservedProductDensity.lean`, `Sampling/QuarticSamplingBudget.lean`, `Sampling/SamplingRankProjectedContainment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B091
import Definitions.Def_OAIE3v2B092

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

theorem exists_bch_integer_coefficients (s : ℕ) :
    ∃ D : ℕ, 0 < D ∧ D ≤ bchCoefficientHeight s ^ (bchBracketSupport s).card ∧
      ∃ c : (w : FreeSemigroup (Fin 2)) → w ∈ bchBracketSupport s → ℤ,
        (∀ w hw, (c w hw : ℚ) = (D : ℚ) * bchBracketCoefficient s w) ∧
        ∀ w hw, (c w hw).natAbs ≤ bchCoefficientHeight s ^ (bchBracketSupport s).card := by
  classical
  let q : bchBracketSupport s → ℚ := fun w => bchBracketCoefficient s w
  have hq : ∀ w, RationalHeightLE (q w) (bchCoefficientHeight s) :=
    fun w => bchBracketCoefficient_height s w.property
  obtain ⟨D, hD, hDb, c, hc, hcb⟩ := exists_bounded_integer_array q hq
  refine ⟨D, hD, ?_, (fun w hw => c ⟨w, hw⟩), ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hDb
  · intro w hw
    exact hc ⟨w, hw⟩
  · intro w hw
    simpa only [Fintype.card_coe] using hcb ⟨w, hw⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget
namespace OAI

section

namespace Erdos3

theorem bchCoordinateHeight_le_exp (s d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hc : (bchCoefficientHeight s : ℝ) ≤ Real.exp p)
    (hm : ((bchBracketSupport s).card : ℝ) ≤ p) :
    (bchCoordinateHeight s d H : ℝ) ≤ Real.exp ((p + 2) ^ (3 * s + 5)) := by
  have hlie := lieCoordinateHeight_le_exp d H s hp hd hH
  have hpbudget : p ≤ (p + 2) ^ (3 * s + 2) := le_power_budget hp (by omega)
  have hprod : ((bchCoefficientHeight s * lieCoordinateHeight d H s : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ (3 * s + 3)) := by
    push_cast
    calc
      _ ≤ Real.exp ((p + 2) ^ (3 * s + 2)) * Real.exp ((p + 2) ^ (3 * s + 2)) :=
        mul_le_mul (hc.trans (Real.exp_le_exp.mpr hpbudget)) hlie
          (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + 2) ^ (3 * s + 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show 3 * s + 3 = (3 * s + 2) + 1 by omega,
          pow_succ (p + 2) (3 * s + 2)]
        nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) (3 * s + 2)]
  have hcard : ((bchBracketSupport s).card : ℝ) ≤ (p + 2) ^ 1 := by
    rw [pow_one]
    linarith
  exact rational_sum_cost_le_exp (bchBracketSupport s).card
    (bchCoefficientHeight s * lieCoordinateHeight d H s) hp (3 * s + 3) 1 hprod hcard

theorem exists_bchCoordinateHeight_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (bchCoordinateHeight s d H : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let C := bchCoefficientHeight s + (bchBracketSupport s).card + 3 * s + 7
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro d H p hp hd hH
  let q : ℝ := p + bchCoefficientHeight s + (bchBracketSupport s).card
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) (bchCoefficientHeight s),
      Nat.cast_nonneg (α := ℝ) (bchBracketSupport s).card]
  have hq : 0 ≤ q := hp.trans hpq
  have hc : (bchCoefficientHeight s : ℝ) ≤ Real.exp q := by
    have h := Real.add_one_le_exp q
    dsimp [q]
    dsimp [q] at h
    linarith [Nat.cast_nonneg (α := ℝ) (bchBracketSupport s).card]
  have hm : ((bchBracketSupport s).card : ℝ) ≤ q := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) (bchCoefficientHeight s)]
  have hbound := bchCoordinateHeight_le_exp s d H hq (hd.trans hpq)
    (hH.trans (Real.exp_le_exp.mpr hpq)) hc hm
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  have hbase : q + 2 ≤ p + C := by
    dsimp [q, C]
    push_cast
    nlinarith
  calc
    (q + 2) ^ (3 * s + 5) ≤ (p + C) ^ (3 * s + 5) :=
      pow_le_pow_left₀ (by linarith) hbase _
    _ ≤ (p + C) ^ C := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def bchBoxMetricConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  ⟨(d + 1) * bchBoxCoordinateBound s d H B,
    mul_nonneg (by positivity) (bchBoxCoordinateBound_nonneg s d H B.coe_nonneg)⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem exists_bchBoxMetricConstant_exp_bound (s r : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (B : ℝ) ≤ Real.exp ((p + 2) ^ r) →
      (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hheight⟩ := exists_bchCoordinateHeight_exp_budget s
  let D := C + 2 * s + r + 10
  refine ⟨D, by dsimp [D]; omega, ?_⟩
  intro d H B p hp hd hH hB
  let t : ℝ := p + D
  have hD3 : (3 : ℝ) ≤ D := by exact_mod_cast (show 3 ≤ D by dsimp [D]; omega)
  have ht : 3 ≤ t := by dsimp [t]; linarith
  have hp2 : p + 2 ≤ t := by dsimp [t]; linarith
  have hd1 : (d : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hs1 : (s : ℝ) + 1 ≤ t := by
    have h : (s : ℝ) + 1 ≤ D := by exact_mod_cast (show s + 1 ≤ D by dsimp [D]; omega)
    dsimp [t]
    linarith
  have hbase : 2 * (d : ℝ) + 1 ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hpoly : ((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s ≤
      t ^ (2 * s + 5) := by
    calc
      _ ≤ t * (t * (t ^ 2) ^ s) * t ^ 2 * t := by
        gcongr <;> linarith
      _ = _ := by rw [← pow_mul, pow_add]; ring
  have hpolyexp : ((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s ≤
      Real.exp (t ^ (D - 1)) := by
    apply hpoly.trans
    apply (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
      (by dsimp [D]; omega : 2 * s + 5 ≤ D - 1)).trans
    linarith [Real.add_one_le_exp (t ^ (D - 1))]
  have hcoef : (bchCoordinateHeight s d H : ℝ) ≤ Real.exp (t ^ (D - 1)) := by
    apply (hheight d H p hp hd hH).trans
    apply Real.exp_le_exp.mpr
    have hCD : (C : ℝ) ≤ D := by exact_mod_cast (show C ≤ D by dsimp [D]; omega)
    apply (pow_le_pow_left₀ (by positivity) (show p + C ≤ t by dsimp [t]; linarith) C).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega)
  have hlength : ((s * (2 * d + 1) : ℕ) : ℝ) ≤ t ^ 3 := by
    push_cast
    calc
      _ ≤ t * t ^ 2 := mul_le_mul (by linarith) hbase (by positivity) (by linarith)
      _ = _ := by ring
  have hinput : (B : ℝ) ^ (s * (2 * d + 1)) ≤ Real.exp (t ^ (D - 1)) := by
    calc
      _ ≤ (Real.exp ((p + 2) ^ r)) ^ (s * (2 * d + 1)) :=
        pow_le_pow_left₀ B.coe_nonneg hB _
      _ = Real.exp (((s * (2 * d + 1) : ℕ) : ℝ) * (p + 2) ^ r) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (t ^ 3 * t ^ r) := Real.exp_le_exp.mpr
        (mul_le_mul hlength (pow_le_pow_left₀ (by linarith) hp2 r) (by positivity) (by positivity))
      _ = Real.exp (t ^ (r + 3)) := by rw [← pow_add, Nat.add_comm 3 r]
      _ ≤ Real.exp (t ^ (D - 1)) := Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith) (by dsimp [D]; omega))
  change ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B ≤ _
  unfold bchBoxCoordinateBound
  push_cast
  calc
    _ = (((d : ℝ) + 1) * (((s : ℝ) + 1) * (2 * d + 1) ^ s) * (2 * d) * s) *
        bchCoordinateHeight s d H * (B : ℝ) ^ (s * (2 * d + 1)) := by ring
    _ ≤ Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) * Real.exp (t ^ (D - 1)) :=
      mul_le_mul (mul_le_mul hpolyexp hcoef (by positivity) (by positivity)) hinput
        (by positivity) (by positivity)
    _ = Real.exp (3 * t ^ (D - 1)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (t ^ D) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ t * t ^ (D - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [D]; omega : 1 ≤ D)]
    _ = _ := rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchBoxCoordinateBound_le_bchBoxMetricConstant (s d H : ℕ) (B : ℝ≥0) :
    bchBoxCoordinateBound s d H B ≤ (bchBoxMetricConstant s d H B : ℝ) := by
  change bchBoxCoordinateBound s d H B ≤ ((d : ℝ) + 1) * bchBoxCoordinateBound s d H B
  have := bchBoxCoordinateBound_nonneg s d H B.coe_nonneg
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedReconstruction
namespace OAI

section

namespace Erdos3

open Module
open scoped NNReal TensorProduct

noncomputable def rationalReconstructionLipschitzBound (s d n H : ℕ) (ℓ B : ℝ≥0) : ℝ≥0 :=
  let C := bchLogMetricConstant s n H 1
  let K := coordinateLipschitzBound d n (rationalSolveHeight n H) * (n + 1) * C
  max (ℓ * (2 * K)) (2 * B / (C⁻¹ / 2))

open NilpotentLieBCHGroup

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReconstructionBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_rationalReconstructionLipschitzBound_exp (s : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (d n H : ℕ) (ℓ B : ℝ≥0) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (n : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (ℓ : ℝ) ≤ Real.exp p → (B : ℝ) ≤ Real.exp p →
      (rationalReconstructionLipschitzBound s d n H ℓ B : ℝ) ≤ Real.exp ((p + N) ^ N) := by
  obtain ⟨D, hD, hbox⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  let N := D + 20
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro d n H ℓ B p hp hd hn hH hℓ hB
  let t := p + N
  let q := t ^ (N - 1)
  have ht : 5 ≤ t := by
    have : (20 : ℝ) ≤ N := by exact_mod_cast (show 20 ≤ N by dsimp [N]; omega)
    dsimp [t]
    linarith
  have hq1 : 1 ≤ q := one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
  have hpq : p ≤ q := by
    apply (show p ≤ t from le_add_of_nonneg_right (Nat.cast_nonneg N)).trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t)
      (show 1 ≤ N - 1 by dsimp [N]; omega)
  have hpe : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hpq
  have htwo : (2 : ℝ) ≤ Real.exp q := by
    linarith [Real.add_one_le_exp q]
  let C := bchLogMetricConstant s n H 1
  have hC : (C : ℝ) ≤ Real.exp q := by
    have hbc := (bchBoxCoordinateBound_le_bchBoxMetricConstant s n H 1).trans
      (hbox n H 1 p hp hn hH (by simp only [NNReal.coe_one, pow_zero]; exact Real.one_le_exp (by norm_num)))
    change bchBoxCoordinateBound s n H 1 ≤ Real.exp ((p + D) ^ D) at hbc
    have hqt : (p + D) ^ D + 1 ≤ q := by
      calc
        (p + D) ^ D + 1 ≤ t ^ D + t ^ D := by
          gcongr
          · dsimp [t, N]; push_cast; linarith
          · exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ t)
        _ ≤ t * t ^ D := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ t) D]
        _ = t ^ (D + 1) := (pow_succ' t D).symm
        _ ≤ q := pow_le_pow_right₀ (by linarith) (by dsimp [N]; omega)
    change bchBoxCoordinateBound s n H 1 + 1 ≤ Real.exp q
    calc
      _ ≤ Real.exp ((p + D) ^ D) + Real.exp ((p + D) ^ D) := by
        linarith [Real.one_le_exp (by positivity : 0 ≤ (p + D) ^ D)]
      _ ≤ Real.exp ((p + D) ^ D) * Real.exp 1 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        nlinarith [Real.exp_pos ((p + D) ^ D)]
      _ = Real.exp ((p + D) ^ D + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hqt
  let A := coordinateLipschitzBound d n (rationalSolveHeight n H)
  have hA : (A : ℝ) ≤ Real.exp q := by
    have hpp : p ≤ (p + 2) ^ 5 := le_power_budget hp (by decide)
    have hA' := coordinateLipschitzBound_le_exp d n (rationalSolveHeight n H)
      (by positivity : 0 ≤ (p + 2) ^ 5) (hd.trans hpp) (hn.trans hpp)
      (by exact_mod_cast rationalSolveHeight_le_budget n H hp hn hH)
    apply hA'.trans
    apply Real.exp_le_exp.mpr
    apply (shifted_power_budget_le hp 5 2).trans
    change (p + 2) ^ 14 ≤ q
    calc
      _ ≤ t ^ 14 := pow_le_pow_left₀ (by linarith) (by dsimp [t, N]; push_cast; linarith) 14
      _ ≤ q := pow_le_pow_right₀ (by linarith) (by dsimp [N]; omega)
  have hdim : (n : ℝ) + 1 ≤ Real.exp q :=
    (show (n : ℝ) + 1 ≤ p + 1 by linarith).trans ((Real.add_one_le_exp p).trans hpe)
  have hfirst : (ℓ : ℝ) * (2 * ((A : ℝ) * ((n : ℝ) + 1) * C)) ≤ Real.exp (5 * q) := by
    calc
      _ ≤ Real.exp q * (Real.exp q * (Real.exp q * Real.exp q * Real.exp q)) := by
        gcongr
        · exact hℓ.trans hpe
      _ = Real.exp (5 * q) := by simp only [← Real.exp_add]; congr 1; ring
  have hsecond : 2 * (B : ℝ) / ((C : ℝ)⁻¹ / 2) ≤ Real.exp (5 * q) := by
    calc
      _ = 2 * 2 * (B : ℝ) * C := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      _ ≤ Real.exp q * Real.exp q * Real.exp q * Real.exp q := by gcongr; exact hB.trans hpe
      _ = Real.exp (4 * q) := by simp only [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (5 * q) := Real.exp_le_exp.mpr (by linarith)
  have hmax : (rationalReconstructionLipschitzBound s d n H ℓ B : ℝ) ≤ Real.exp (5 * q) := by
    change max ((ℓ : ℝ) * (2 * ((A : ℝ) * ((n : ℝ) + 1) * C)))
      (2 * (B : ℝ) / ((C : ℝ)⁻¹ / 2)) ≤ _
    exact max_le hfirst hsecond
  apply hmax.trans
  apply Real.exp_le_exp.mpr
  calc
    5 * q ≤ t * q := mul_le_mul_of_nonneg_right ht (by dsimp [q]; positivity)
    _ = (p + N) ^ N := by dsimp [q, t]; rw [← pow_succ', Nat.sub_add_cancel (by dsimp [N]; omega)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedTranslation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem translate_sub_coefficient_mem (w : σ → ℕ) (hw : ∀ i, 0 < w i) (h : σ → ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (α : σ →₀ ℕ) :
    coefficients (translate h p - p) α ∈ F.layer (Finsupp.weight w α + 1) := by
  rw [coefficients_translate_sub]
  apply Submodule.sum_mem
  intro β hβ
  by_cases hc : (polynomialTranslate h (MvPolynomial.monomial β 1) -
      MvPolynomial.monomial β 1).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h w hw β).2
      (MvPolynomial.mem_support_iff.mpr hc))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrTorusApproximation
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

@[simp] theorem rank_ndilate (B : Set N) (t : ℝ≥0) :
    (B.ndilate t).rank = B.rank := rfl

@[simp] theorem ndilate_one (B : Set N) : B.ndilate 1 = B := by simp [ndilate]

@[simp] theorem ndilate_ndilate (B : Set N) (s t : ℝ≥0) :
    (B.ndilate s).ndilate t = B.ndilate (t * s) := by simp [ndilate]

theorem carrier_ndilate_mono {B : Set N} {s t : ℝ≥0} (hst : s ≤ t) :
    (B.ndilate s).carrier ⊆ (B.ndilate t).carrier :=
  B.dilate_mono s.coe_nonneg (by exact_mod_cast hst)

def IsRankRegular (B : Set N) : Prop :=
  let d : ℕ := 2 * max B.rank 1
  ∀ kappa : ℝ≥0,
    kappa ≤ 1 / (100 * (d : ℝ≥0)) →
      (1 - 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ) ≤
          ((B.ndilate (1 - kappa)).carrier.card : ℝ) ∧
      ((B.ndilate (1 + kappa)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ)

theorem isRankRegular_ndilate_iff (B : Set N) (rho : ℝ≥0) :
    (B.ndilate rho).IsRankRegular ↔
      let d : ℕ := 2 * max B.rank 1
      ∀ kappa : ℝ≥0,
        kappa ≤ 1 / (100 * (d : ℝ≥0)) →
          (1 - 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) ≤
              ((B.ndilate ((1 - kappa) * rho)).carrier.card : ℝ) ∧
          ((B.ndilate ((1 + kappa) * rho)).carrier.card : ℝ) ≤
              (1 + 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.ndilate rho).carrier.card : ℝ) := by
  simp [IsRankRegular, mul_comm]

theorem log_card_growth_lt_five_mul_rank (B : Set N) (hB : 0 < B.radius) :
    Real.log ((B.ndilate (5 / 4)).carrier.card : ℝ) -
        Real.log ((B.ndilate (1 / 4)).carrier.card : ℝ) <
      5 * (2 * max B.rank 1 : ℕ) := by
  classical
  let d : ℕ := 2 * max B.rank 1
  have hcard : (B.ndilate (5 / 4)).carrier.card ≤
      9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card := by
    calc
      (B.ndilate (5 / 4)).carrier.card ≤ (B.ndilate 2).carrier.card :=
        Finset.card_le_card (carrier_ndilate_mono
          (show (5 / 4 : NNReal) ≤ 2 by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
            norm_num))
      _ ≤ 9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card :=
        by simpa [ndilate] using card_two_le_nine_pow_three_rank_mul_card_quarter B hB
  have hsmall_pos : (0 : ℝ) < (B.ndilate (1 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (1 / 4)).carrier_nonempty.card_pos
  have hlarge_pos : (0 : ℝ) < (B.ndilate (5 / 4)).carrier.card := by
    exact_mod_cast (B.ndilate (5 / 4)).carrier_nonempty.card_pos
  have hlog := Real.log_le_log hlarge_pos (show
      ((B.ndilate (5 / 4)).carrier.card : ℝ) ≤
        ((9 ^ (3 * B.rank) * (B.ndilate (1 / 4)).carrier.card : ℕ) : ℝ) by
      exact_mod_cast hcard)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) hsmall_pos.ne',
    Real.log_pow] at hlog
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by simp [d])
  have hlog9 : Real.log (9 : ℝ) < 10 / 3 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9)
      (by norm_num : (9 : ℝ) ≤ 2 ^ 4)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_lt_d9]
  have hmain : (3 * B.rank : ℕ) * Real.log (9 : ℝ) < 5 * d := by
    have hpos : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
    have hrank : (B.rank : ℝ) ≤ (max B.rank 1 : ℕ) := by exact_mod_cast le_max_left B.rank 1
    push_cast
    calc
      3 * (B.rank : ℝ) * Real.log 9 ≤ 3 * (max B.rank 1 : ℕ) * Real.log 9 := by gcongr
      _ < 3 * (max B.rank 1 : ℕ) * (10 / 3) := by gcongr
      _ = 5 * d := by dsimp [d]; push_cast; ring
  dsimp [d] at hmain ⊢
  linarith

noncomputable def normalizedLogCard (B : Set N) (s : ℝ) : ℝ :=
  Real.log ((B.ndilate s.toNNReal).carrier.card : ℝ) /
    (2 * max B.rank 1 : ℕ)

theorem normalizedLogCard_monotone (B : Set N) :
    Monotone B.normalizedLogCard := by
  intro s t hst
  dsimp [normalizedLogCard]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.log_le_log
  · exact_mod_cast (B.ndilate s.toNNReal).carrier_nonempty.card_pos
  · exact_mod_cast Finset.card_le_card
      (carrier_ndilate_mono (B := B) (Real.toNNReal_mono hst))

theorem normalizedLogCard_buffer_growth (B : Set N) (hB : 0 < B.radius) :
    B.normalizedLogCard (5 / 4) - B.normalizedLogCard (1 / 4) < 5 := by
  classical
  have h := log_card_growth_lt_five_mul_rank B hB
  have hd : (0 : ℝ) < (2 * max B.rank 1 : ℕ) := by positivity
  have h54 : Real.toNNReal (5 / 4 : ℝ) = (5 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have h14 : Real.toNNReal (1 / 4 : ℝ) = (1 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  dsimp [normalizedLogCard]
  rw [h54, h14]
  rw [div_sub_div_same]
  exact (div_lt_iff₀ hd).2 (by simpa [mul_comm] using h)

theorem exists_rankRegular_ndilate (B : Set N) (hB : 0 < B.radius) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      (B.ndilate rho).IsRankRegular := by
  classical
  let d : ℕ := 2 * max B.rank 1
  obtain ⟨r, hr, hlip⟩ := exists_regular_point_of_monotone
    B.normalizedLogCard (normalizedLogCard_monotone B)
      (normalizedLogCard_buffer_growth B hB)
  let rho : NNReal := r.toNNReal
  have hrho : (rho : ℝ) = r := Real.coe_toNNReal r (by linarith [hr.1])
  have hrho_half : (1 / 2 : NNReal) ≤ rho := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.1
  have hrho_one : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.2
  refine ⟨rho, hrho_half, hrho_one, ?_⟩
  rw [isRankRegular_ndilate_iff]
  dsimp only [rank_ndilate]
  intro kappa hkappa
  have hdposN : 0 < d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hkappa_real : (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
    exact_mod_cast hkappa
  let sminus : NNReal := (1 - kappa) * rho
  let splus : NNReal := (1 + kappa) * rho
  have hkreal : (kappa : ℝ) ≤ 1 / 100 := by
    calc
      (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := hkappa_real
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hd_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by dsimp [d]; omega)
        nlinarith
  have hrho_real : (1 / 2 : ℝ) ≤ rho ∧ (rho : ℝ) ≤ 1 := by
    exact ⟨by exact_mod_cast hrho_half, by exact_mod_cast hrho_one⟩
  have hsminus_buf : (sminus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hk_lower : (99 / 100 : ℝ) ≤ 1 - (kappa : ℝ) := by
      nlinarith
    constructor
    · calc
        (1 / 4 : ℝ) ≤ (99 / 100) * (1 / 2) := by norm_num
        _ ≤ (1 - (kappa : ℝ)) * (rho : ℝ) := by
          exact mul_le_mul hk_lower hrho_real.1 (by norm_num)
            (sub_nonneg.mpr (by exact_mod_cast hkappa_one))
    · calc
        (1 - (kappa : ℝ)) * (rho : ℝ) ≤ 1 * rho :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 (by positivity)) (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrho_real.2 (by norm_num)
        _ ≤ 5 / 4 := by norm_num
  have hsplus_buf : (splus : ℝ) ∈ _root_.Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [splus]
    constructor <;> nlinarith
  have hdistminus : |(sminus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 - (kappa : ℝ)) * (rho : ℝ) - rho = -(kappa * rho) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hdistplus : |(splus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [splus]
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 + (kappa : ℝ)) * (rho : ℝ) - rho = kappa * rho by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hlipminus := hlip (sminus : ℝ) hsminus_buf
  have hlipplus := hlip (splus : ℝ) hsplus_buf
  simp only [normalizedLogCard, Real.toNNReal_coe,
    show r.toNNReal = rho by rfl] at hlipminus hlipplus
  change
    |Real.log ((B.ndilate sminus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(sminus : ℝ) - r| at hlipminus
  change
    |Real.log ((B.ndilate splus).carrier.card : ℝ) / d -
      Real.log ((B.ndilate rho).carrier.card : ℝ) / d| ≤
        60 * |(splus : ℝ) - r| at hlipplus
  rw [div_sub_div_same, abs_div, abs_of_pos hdpos] at hlipminus hlipplus
  have hlogminus :
      Real.log ((B.ndilate rho).carrier.card : ℝ) -
          Real.log ((B.ndilate sminus).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipminus
    calc
      _ ≤ |Real.log ((B.ndilate sminus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 60 * |(sminus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  have hlogplus :
      Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipplus
    calc
      _ ≤ |Real.log ((B.ndilate splus).carrier.card : ℝ) -
          Real.log ((B.ndilate rho).carrier.card : ℝ)| := le_abs_self _
      _ ≤ 60 * |(splus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  let u : ℝ := 100 * d * (kappa : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      100 * (d : ℝ) * (kappa : ℝ) ≤
          100 * d * (1 / (100 * d)) := by gcongr
      _ = 1 := by field_simp
  have hslope : 60 * d * (kappa : ℝ) = (3 / 5 : ℝ) * u := by
    dsimp [u]
    ring
  constructor
  · change (1 - u) * ((B.ndilate rho).carrier.card : ℝ) ≤
      ((B.ndilate sminus).carrier.card : ℝ)
    by_cases hu : u = 1
    · rw [hu]
      norm_num
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu
      have honeu : 0 < 1 - u := sub_pos.mpr hu_lt
      have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
        exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
      have hinner : (0 : ℝ) < (B.ndilate sminus).carrier.card := by
        exact_mod_cast (B.ndilate sminus).carrier_nonempty.card_pos
      rw [← Real.log_le_log_iff (mul_pos honeu hcenter) hinner]
      rw [Real.log_mul (sub_ne_zero.mpr (Ne.symm hu)) hcenter.ne']
      have hlogone := Real.log_le_sub_one_of_pos honeu
      rw [hslope] at hlogminus
      nlinarith
  · change ((B.ndilate splus).carrier.card : ℝ) ≤
      (1 + u) * ((B.ndilate rho).carrier.card : ℝ)
    have hcenter : (0 : ℝ) < (B.ndilate rho).carrier.card := by
      exact_mod_cast (B.ndilate rho).carrier_nonempty.card_pos
    have houter : (0 : ℝ) < (B.ndilate splus).carrier.card := by
      exact_mod_cast (B.ndilate splus).carrier_nonempty.card_pos
    rw [← Real.log_le_log_iff houter (mul_pos (by linarith) hcenter)]
    rw [Real.log_mul (by linarith) hcenter.ne']
    have hlogone := Real.le_log_one_add_of_nonneg hu0
    have hfrac : (3 / 5 : ℝ) * u ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    rw [hslope] at hlogplus
    linarith

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationWidth (B : Set N) (rho : ℝ≥0) : ℝ≥0 :=
  rho * ⟨B.radius, B.radius_nonneg⟩

noncomputable def upperApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) : ℝ :=
  chordBoxCutoff B.radius (B.approximationWidth rho) (fun r : B.frequencies => character r x)

noncomputable def lowerApprox (B : Set N) (rho : ℝ≥0) (x : ZMod N) : ℝ :=
  chordBoxCutoff (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)
    (fun r : B.frequencies => character r x)

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem add_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x + y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using add_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem sub_mem_ndilate {B : Set N} {r s : ℝ≥0} {x y : ZMod N}
    (hx : x ∈ B.ndilate r) (hy : y ∈ B.ndilate s) :
    x - y ∈ B.ndilate (r + s) := by
  simpa only [ndilate, NNReal.coe_add] using sub_mem_dilate r.coe_nonneg s.coe_nonneg hx hy

theorem uniformMass_translation_le_shell (B : Set N) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1) {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      (((B.ndilate (1 + kappa)).carrier.card : ℝ) - (B.ndilate (1 - kappa)).carrier.card) /
        B.carrier.card := by
  apply Erdos3.uniformMass_translation_le_shell
  · intro x hx
    constructor
    · have h := carrier_ndilate_mono (B := B) (show 1 - kappa ≤ 1 from tsub_le_self) hx
      simpa only [ndilate_one] using h
    · have h := sub_mem_ndilate (B := B) hx ht
      simpa only [tsub_add_cancel_of_le hkappa, ndilate_one, mem_iff, mem_carrier] using h
  · intro x hx
    rcases hx with hx | hx
    · have h := carrier_ndilate_mono (B := B) (show (1 : ℝ≥0) ≤ 1 + kappa from le_self_add)
      apply h
      simpa only [ndilate_one] using hx
    · have h := add_mem_ndilate (B := B) (r := 1) (s := kappa)
        (x := x - t) (y := t) (by simpa only [ndilate_one, mem_iff, mem_carrier] using hx) ht
      simpa only [sub_add_cancel, mem_iff, mem_carrier] using h

theorem uniformMass_translation_le_of_rankRegular {B : Set N} (hreg : B.IsRankRegular)
    {kappa : ℝ≥0} (hkappa : kappa ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {t : ZMod N} (ht : t ∈ B.ndilate kappa) :
    ∑ x : ZMod N, |realUniformMass B.carrier (x - t) - realUniformMass B.carrier x| ≤
      400 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
    · positivity
  have hcards := hreg kappa hkappa
  have hcenter : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  apply (uniformMass_translation_le_shell B hkappa_one ht).trans
  rw [div_le_iff₀ hcenter]
  push_cast at hcards ⊢
  nlinarith [hcards.1, hcards.2]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

def whole : Set N := ofFrequencies {0} 1 (by norm_num)

@[simp] theorem rank_whole : (whole : Set N).rank = 1 := by simp [whole]

@[simp] theorem radius_whole : (whole : Set N).radius = 1 := rfl

@[simp] theorem carrier_whole : (whole : Set N).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [whole, mem_carrier, ofFrequencies]

theorem exists_controlled_regular_subdilate (B : Set N) (hB : 0 < B.radius)
    (r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ C : Set N, C.frequencies = B.frequencies ∧ C.IsRankRegular ∧
      (r : ℝ) * B.radius / 2 ≤ C.radius ∧ C.radius ≤ r * B.radius ∧
      C.carrier ⊆ (B.ndilate r).carrier ∧
      ((r : ℝ) / 4) ^ (4 * B.rank) * (B.carrier.card : ℝ) ≤ C.carrier.card := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1R : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hB0 : 0 < (B.ndilate r).radius := by
    rw [radius_ndilate]
    exact mul_pos hrR hB
  obtain ⟨rho, hrho0, hrho1, hreg⟩ := exists_rankRegular_ndilate (B.ndilate r) hB0
  let C := (B.ndilate r).ndilate rho
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have hC : C.radius = (rho : ℝ) * ((r : ℝ) * B.radius) := by simp only [C, radius_ndilate]
  refine ⟨C, rfl, hreg, ?_, ?_, ?_, ?_⟩
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · rw [hC]
    nlinarith [mul_nonneg hrR.le hB.le]
  · have h := carrier_ndilate_mono (B := B.ndilate r) hrho1
    simpa only [ndilate_one] using h
  · have hprod : 0 < (rho : ℝ) * r := mul_pos (by linarith) hrR
    have hprod1 : (rho : ℝ) * r ≤ 1 := by nlinarith
    have hvol := relative_card_lower_bound B hB hprod hprod1
    have hlower : (r : ℝ) / 4 ≤ ((rho : ℝ) * r) / 2 := by nlinarith
    have hcost := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (show (0 : ℝ) ≤ r / 4 by positivity) hlower (4 * B.rank))
      (Nat.cast_nonneg B.carrier.card : (0 : ℝ) ≤ B.carrier.card)
    have hfull := hcost.trans hvol
    simpa only [C, ndilate, dilate_dilate] using hfull

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

@[simp] theorem carrier_ndilate_whole (t : ℝ≥0) :
    ((whole : Set N).ndilate t).carrier = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro x
  simp [mem_carrier, whole, ndilate, ofFrequencies, dilate]

theorem isRankRegular_whole : (whole : Set N).IsRankRegular := by
  intro kappa _
  simp only [rank_whole, max_self, Nat.mul_one, Nat.cast_ofNat, carrier_whole,
    carrier_ndilate_whole]
  have hcard : (0 : ℝ) ≤ (Finset.univ : Finset (ZMod N)).card := Nat.cast_nonneg _
  constructor <;> nlinarith [mul_nonneg kappa.coe_nonneg hcard]

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.CyclicBohr.Set

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def torusUpperApprox (B : Set N) (rho : ℝ≥0) :
    (B.frequencies → CircleFourier.Circle) → ℝ :=
  torusChordCutoff B.radius (B.approximationWidth rho)

noncomputable def torusLowerApprox (B : Set N) (rho : ℝ≥0) :
    (B.frequencies → CircleFourier.Circle) → ℝ :=
  torusChordCutoff (B.radius - (rho : ℝ) * B.radius) (B.approximationWidth rho)

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
namespace OAI

section

open _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {N : ℕ} [NeZero N]

theorem convolutionPower_realUniformMass_support
    (B : CyclicBohr.Set N) (σ : ℝ≥0) :
    ∀ n x, convolutionPower (realUniformMass (B.ndilate σ).carrier) n x ≠ 0 →
      x ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by
        simpa using
          (realUniformMass_ne_zero_iff (singleton_nonempty 0) x).mp hx
      subst x
      simpa only [Nat.cast_zero, zero_mul, CyclicBohr.Set.mem_iff,
        CyclicBohr.Set.mem_carrier] using (B.ndilate 0).zero_mem
  | succ n ihn =>
      intro x hx
      rw [convolutionPower_succ, massConvolution] at hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hypow : convolutionPower (realUniformMass (B.ndilate σ).carrier) n y ≠ 0 :=
        (mul_ne_zero_iff.mp hy).1
      have hysmall : realUniformMass (B.ndilate σ).carrier (x - y) ≠ 0 :=
        (mul_ne_zero_iff.mp hy).2
      have hyB := ihn y hypow
      have hxyB : x - y ∈ (B.ndilate σ).carrier :=
        (realUniformMass_ne_zero_iff
          (B.ndilate σ).carrier_nonempty (x - y)).mp hysmall
      have hadd := CyclicBohr.Set.add_mem_ndilate hyB hxyB
      have hxsum : y + (x - y) = x := by simp
      rw [hxsum] at hadd
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_carrier] using hadd

def bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) : (ZMod N) → ℝ :=
  massConvolution
    (realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
    (convolutionPower (realUniformMass (B.ndilate σ).carrier) n)

theorem bohrSmoothingMeasure_nonneg (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (x : (ZMod N)) :
    0 ≤ bohrSmoothingMeasure B σ n x := by
  exact massConvolution_nonneg
    (realUniformMass_nonneg _)
    (convolutionPower_nonneg (realUniformMass_nonneg _) n) x

theorem sum_bohrSmoothingMeasure (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) :
    ∑ x : (ZMod N), bohrSmoothingMeasure B σ n x = 1 := by
  rw [bohrSmoothingMeasure, sum_massConvolution,
    sum_realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty,
    sum_convolutionPower
      (sum_realUniformMass (B.ndilate σ).carrier_nonempty), one_mul]

theorem bohrSmoothingMeasure_apply_of_mem
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) {x : (ZMod N)} (hx : x ∈ B.carrier) :
    bohrSmoothingMeasure B σ n x =
      (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
  rw [bohrSmoothingMeasure, massConvolution_comm]
  simp only [massConvolution]
  calc
    ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          realUniformMass (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier (x - t) =
        ∑ t : (ZMod N), convolutionPower (realUniformMass (B.ndilate σ).carrier) n t *
          (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hνt :
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t = 0
      · simp [hνt]
      · have htB : t ∈ (B.ndilate ((n : ℝ≥0) * σ)).carrier :=
          convolutionPower_realUniformMass_support B σ n t hνt
        have hxt : x - t ∈
            (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier := by
          exact CyclicBohr.Set.sub_mem_ndilate
            (B := B) (r := 1) (s := (n : ℝ≥0) * σ)
            (by simpa only [CyclicBohr.Set.ndilate_one, CyclicBohr.Set.mem_iff,
              CyclicBohr.Set.mem_carrier] using hx) htB
        rw [realUniformMass_apply_mem hxt]
    _ = (∑ t : (ZMod N),
          convolutionPower (realUniformMass (B.ndilate σ).carrier) n t) *
        (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (((B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [sum_convolutionPower
        (sum_realUniformMass (B.ndilate σ).carrier_nonempty)]
      simp

theorem card_dilate_one_add_le_two_mul
    {B : CyclicBohr.Set N} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier.card ≤
      2 * B.carrier.card := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  let d : ℕ := 2 * max B.rank 1
  have hcards := hreg κ (by simpa [κ, d] using hsmall)
  have hfactor : (1 + 100 * (d : ℝ) * (κ : ℝ)) ≤ 2 := by
    have hsmallR : (κ : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
      exact_mod_cast (show κ ≤ 1 / (100 * (d : ℝ≥0)) by
        simpa [κ, d] using hsmall)
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
    calc
      1 + 100 * (d : ℝ) * (κ : ℝ) ≤
          1 + 100 * (d : ℝ) * (1 / (100 * (d : ℝ))) := by gcongr
      _ = 2 := by field_simp; ring
  have hcardR :
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.ndilate (1 + κ)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (κ : ℝ)) * (B.carrier.card : ℝ) := by
        simpa [κ, d] using hcards.2
      _ ≤ 2 * (B.carrier.card : ℝ) := by gcongr
  exact_mod_cast hcardR

theorem norm_massCoeff_bohrSmoothingMeasure_le
    (B : CyclicBohr.Set N) (σ : ℝ≥0) (n : ℕ) (ψ : AddChar (ZMod N) ℂ) :
    ‖massCoeff (bohrSmoothingMeasure B σ n) ψ‖ ≤
      ‖massCoeff (realUniformMass (B.ndilate σ).carrier) ψ‖ ^ n := by
  rw [bohrSmoothingMeasure, massCoeff_massConvolution,
    massCoeff_convolutionPower, norm_mul, norm_pow]
  have houter :
      ‖massCoeff (realUniformMass
        (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier) ψ‖ ≤ 1 := by
    simpa [sum_realUniformMass
      (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty] using
      norm_massCoeff_le_sum
        (w := realUniformMass
          (B.ndilate (1 + (n : ℝ≥0) * σ)).carrier)
        (realUniformMass_nonneg _) ψ
  exact mul_le_of_le_one_left (by positivity) houter

end

end Erdos3

end

section

open AddChar _root_.Finset
open scoped BigOperators NNReal

namespace Erdos3

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

variable {N : ℕ} [NeZero N]

theorem norm_one_sub_le_of_mem_largeSpectrum
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {eta : ℝ} (heta : 0 < eta)
    {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier eta)
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤
      400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) / eta := by
  classical
  let F : ℂ := ∑ x : (ZMod N), (realUniformMass C.carrier x : ℂ) * psi x
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hFnorm : ‖F‖ = ‖Chang.spectrumSum C.carrier psi‖ / C.carrier.card := by
    dsimp [F]
    rw [normalizedSpectrum_eq, norm_mul]
    simp [div_eq_inv_mul]
  have hlarge : eta ≤ ‖F‖ := by
    rw [hFnorm, le_div_iff₀ hcard]
    exact Chang.mem_largeSpectrum.mp hpsi
  have hphase :
      ‖1 - psi t‖ * ‖F‖ ≤
        ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
    rw [← norm_mul, normalizedSpectrum_translate C.carrier psi t]
    calc
      ‖∑ x : (ZMod N),
          ((realUniformMass C.carrier x -
              realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ ≤
          ∑ x : (ZMod N),
            ‖((realUniformMass C.carrier x -
                realUniformMass C.carrier (x - t) : ℝ) : ℂ) * psi x‖ :=
        norm_sum_le _ _
      _ = ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp
  have htranslation :=
    CyclicBohr.Set.uniformMass_translation_le_of_rankRegular
      hreg hsigma ht
  have hmul :
      ‖1 - psi t‖ * eta ≤
        400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
    calc
      ‖1 - psi t‖ * eta ≤ ‖1 - psi t‖ * ‖F‖ :=
        mul_le_mul_of_nonneg_left hlarge (norm_nonneg _)
      _ ≤ ∑ x : (ZMod N),
          |realUniformMass C.carrier (x - t) -
            realUniformMass C.carrier x| := hphase
      _ ≤ 400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := htranslation
  exact (le_div_iff₀ heta).2 hmul

theorem norm_one_sub_le_of_mem_largeSpectrum_half
    {C : CyclicBohr.Set N} (hreg : C.IsRankRegular) {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier (1 / 2))
    {t : (ZMod N)} (ht : t ∈ (C.ndilate sigma).carrier) :
    ‖1 - psi t‖ ≤ 800 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  classical
  have h := norm_one_sub_le_of_mem_largeSpectrum hreg (eta := (1 / 2 : ℝ))
    (by norm_num) hsigma hpsi ht
  convert h using 1
  ring

end

end Erdos3

end

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

noncomputable def initialSamplingScale (B : Set N) : ℝ≥0 :=
  1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicRelativeChang
namespace OAI

section

open _root_.Finset Real
open scoped BigOperators NNReal

namespace Erdos3.RelativeChangSanders

noncomputable section

variable {N : ℕ} [NeZero N]

def localChangDimension (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) : ℝ :=
  2 * (1 + log (2 * (B.carrier.card : ℝ) / X.card)) / eta ^ 2

def localChangCap (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) : ℕ :=
  ⌈localChangDimension B X eta⌉₊ + 1

def localChangBaseScale (B : CyclicBohr.Set N) (X : Finset (ZMod N))
    (eta : ℝ) : NNReal :=
  (100 * ((2 * max B.rank 1 : ℕ) : NNReal) *
    (((2 * localChangCap B X eta + 1 : ℕ) : NNReal)))⁻¹

theorem exists_relativeLargeSpectrum_cover
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    (X : Finset (ZMod N)) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ rho : NNReal, ∃ C : CyclicBohr.Set N,
      ∃ Delta : Finset (AddChar (ZMod N) ℂ),
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.ndilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        ∀ psi ∈ Chang.largeSpectrum X eta,
          ∃ z ∈ Delta.addSpan,
            ∃ s ∈ Chang.largeSpectrum C.carrier (1 / 2), psi = z + s := by
  classical
  let D : ℝ := localChangDimension B X eta
  let k : ℕ := localChangCap B X eta
  let d : ℕ := 2 * max B.rank 1
  let a : NNReal := localChangBaseScale B X eta
  have haPos : 0 < a := by
    dsimp [a, localChangBaseScale]
    positivity
  have haposR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hbasePos : 0 < (B.ndilate a).radius := by
    rw [CyclicBohr.Set.radius_ndilate]
    exact mul_pos haposR hBpos
  obtain ⟨rho, hrhoHalf, hrhoOne, hregular⟩ :=
    CyclicBohr.Set.exists_rankRegular_ndilate (B.ndilate a) hbasePos
  let tau : NNReal := rho * a
  let C : CyclicBohr.Set N := B.ndilate tau
  have hCreg : C.IsRankRegular := by
    simpa [C, tau] using hregular
  have hd : 0 < d := by simp [d]
  have hk : 0 < k := by simp [k, localChangCap]
  have ha : a =
      (100 * (d : NNReal) * (((2 * k + 1 : ℕ) : NNReal)))⁻¹ := by
    simp [a, localChangBaseScale, d, k]
  have hsmall : (((2 * k : ℕ) : NNReal) * tau) ≤
      1 / (100 * (d : NNReal)) := by
    have hkden : (0 : NNReal) < (((2 * k + 1 : ℕ) : NNReal)) := by positivity
    have hdb : (0 : NNReal) < 100 * (d : NNReal) := by positivity
    calc
      (((2 * k : ℕ) : NNReal) * tau) =
          ((2 * k : ℕ) : NNReal) * (rho * a) := rfl
      _ ≤ ((2 * k : ℕ) : NNReal) * (1 * a) := by gcongr
      _ = (((2 * k : ℕ) : NNReal) /
          (((2 * k + 1 : ℕ) : NNReal))) /
            (100 * (d : NNReal)) := by rw [ha]; field_simp
      _ ≤ 1 / (100 * (d : NNReal)) := by
        gcongr
        exact (div_le_one hkden).2 (by
          exact_mod_cast Nat.le_add_right (2 * k) 1)
  let T : Finset (AddChar (ZMod N) ℂ) := Chang.largeSpectrum X eta
  let S : Finset (AddChar (ZMod N) ℂ) :=
    Chang.largeSpectrum C.carrier (1 / 2)
  let w : (ZMod N) → ℝ := Erdos3.bohrSmoothingMeasure B tau (2 * k)
  let outer : Finset (ZMod N) :=
    (B.ndilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier
  let c : ℝ := (outer.card : ℝ)⁻¹
  let R : ℝ := 2 * (B.carrier.card : ℝ) / X.card
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact Erdos3.bohrSmoothingMeasure_nonneg B tau (2 * k) x
  have hw1 : ∑ x : (ZMod N), w x = 1 := by
    exact Erdos3.sum_bohrSmoothingMeasure B tau (2 * k)
  have hwconst : ∀ x ∈ B.carrier, w x = c := by
    intro x hx
    simpa [w, c, outer] using
      (Erdos3.bohrSmoothingMeasure_apply_of_mem B tau (2 * k) hx)
  have hOuterCard : outer.card ≤ 2 * B.carrier.card := by
    simpa [outer, d] using
      (Erdos3.card_dilate_one_add_le_two_mul hBreg (2 * k) hsmall)
  have hOuterPos : 0 < outer.card := by
    exact outer.card_pos.mpr (by
      simpa [outer] using
        (B.ndilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier_nonempty)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hR : (c * X.card)⁻¹ ≤ R := by
    have hOr : (0 : ℝ) < outer.card := by exact_mod_cast hOuterPos
    have hXr : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hOr' : (outer.card : ℝ) ≤ 2 * B.carrier.card := by
      exact_mod_cast hOuterCard
    calc
      (c * (X.card : ℝ))⁻¹ = (outer.card : ℝ) / X.card := by
        dsimp [c]
        field_simp
      _ ≤ (2 * B.carrier.card : ℝ) / X.card :=
        (div_le_div_iff_of_pos_right hXr).2 hOr'
      _ = R := by simp [R]
  have hzero : (0 : AddChar (ZMod N) ℂ) ∈ S := by
    exact zero_mem_chang_largeSpectrum_half C.carrier
  have hneg : ∀ s ∈ S, -s ∈ S := by
    intro s hs
    exact neg_mem_chang_largeSpectrum hs
  have hDk : D < (k : ℝ) := by
    calc
      D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
      _ < ((⌈D⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self ⌈D⌉₊
      _ = (k : ℝ) := by simp [k, localChangCap, D]
  have hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D := by
    intro Gamma hGammaT hGammaMod hGammaCard
    have hq : ∀ psi, psi ∉ S →
        ‖Erdos3.massCoeff w psi‖ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
      intro psi hpsi
      calc
        ‖Erdos3.massCoeff w psi‖ ≤
            ‖Erdos3.massCoeff
              (realUniformMass (B.ndilate tau).carrier) psi‖ ^ (2 * k) := by
          exact Erdos3.norm_massCoeff_bohrSmoothingMeasure_le
            B tau (2 * k) psi
        _ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
          gcongr
          exact (Erdos3.norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
            (B.ndilate tau).carrier (B.ndilate tau).carrier_nonempty psi
              (by simpa [S, C] using hpsi)).le
    have hweighted : IsWeightedDissociated w 1 Gamma := by
      apply hGammaMod.isWeightedDissociated_of_le_quarter_pow
        hw0 hw1 (by positivity) hq hGammaCard
      rw [pow_mul]
      norm_num
    have hcard := card_weightedDissociated_realFinsetIndicator_le
      B.carrier X hXB hX w c R eta hw0 hwconst hc hR heta Gamma
        hweighted (by simpa [T] using hGammaT)
    simpa [D, localChangDimension, R] using hcard
  obtain ⟨Delta, hDeltaT, _, hDeltaCard, hcover⟩ :=
    exists_maximal_addDissociatedMod_card_le S T hzero hneg D k hDk hdim
  refine ⟨rho, C, Delta, hrhoHalf, hrhoOne, ?_, hCreg, ?_, ?_, ?_⟩
  · simp [C, tau, a]
  · simpa [D] using hDeltaCard
  · simpa [T] using hDeltaT
  · simpa [T, S] using hcover

end

end Erdos3.RelativeChangSanders

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

open Module

noncomputable def bchIntegralDenominatorBound (s : ℕ) : ℕ :=
  bchCoefficientHeight s ^ (bchBracketSupport s).card

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_bch_stable_integral_grid (e : Basis ι ℚ L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (l : ℕ) (hl : 0 < l) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound s * H ^ (Fintype.card ι ^ 3) * l ∧
      ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
        lieBCH s a b ∈ coordinateGridModule e B := by
  classical
  obtain ⟨D, hD, hDb, u, hu, _⟩ := exists_bch_integer_coefficients s
  obtain ⟨E, hE, hEb, c, hEcoeff, _⟩ := exists_bounded_integer_array
    (fun ijk : ι × (ι × ι) => lieStructureConstants e ijk.1 ijk.2.1 ijk.2.2)
    (fun ijk => hc ijk.1 ijk.2.1 ijk.2.2)
  have hEb' : E ≤ H ^ (Fintype.card ι ^ 3) := by
    simpa only [Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using hEb
  let B := (D * E) * l
  have hscaled (i j k : ι) :
      ∃ n : ℤ, (B : ℚ) * lieStructureConstants e i j k = (D : ℚ) * n := by
    refine ⟨(l : ℤ) * c (i, j, k), ?_⟩
    simp only [B, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, hEcoeff]
    ring
  refine ⟨B, Nat.mul_pos (Nat.mul_pos hD hE) hl, dvd_mul_left l (D * E),
    Nat.mul_le_mul_right l (Nat.mul_le_mul hDb hEb'), ?_⟩
  intro a ha b hb
  exact lieBCH_mem_of_divisible_brackets_nilpotent (coordinateGridModule e B) D hnil
    (fun x hx y hy => coordinateGrid_bracket_divisible e B D hscaled hx hy)
    (fun w hw => ⟨u w hw, (hu w hw).symm⟩) ha hb

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem lieTreeEval_sub_mem (v w : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (hw : ∀ i, w i ∈ F.layer (d i) 1)
    (hvw : ∀ i, v i - w i ∈ F.layer (d i) 2) (a : FreeMagma I) :
    lieTreeEval v a - lieTreeEval w a ∈
      F.layer (lieTreeWeight d a) (a.length + 1) := by
  induction a using FreeMagma.rec with
  | of i => exact hvw i
  | mul a b ha hb =>
    have h₁ := F.lie_mem ha (F.lieTreeEval_mem_length v d hv b)
    have h₂ := F.lie_mem (F.lieTreeEval_mem_length w d hw a) hb
    have heq : lieTreeEval v (a.mul b) - lieTreeEval w (a.mul b) =
        ⁅lieTreeEval v a - lieTreeEval w a, lieTreeEval v b⁆ +
          ⁅lieTreeEval w a, lieTreeEval v b - lieTreeEval w b⁆ := by
      simp only [lieTreeEval, sub_lie, lie_sub]
      abel
    rw [heq]
    apply Submodule.add_mem
    · simpa only [lieTreeWeight, FreeMagma.length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h₁
    · simpa only [lieTreeWeight, FreeMagma.length, Nat.add_assoc] using h₂

theorem top_lieTreeEval_congr (v w : I → L) (d : I → ℕ)
    (hv : ∀ i, v i ∈ F.layer (d i) 1) (hw : ∀ i, w i ∈ F.layer (d i) 1)
    (hvw : ∀ i, v i - w i ∈ F.layer (d i) 2) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r) :
    lieTreeEval v a = lieTreeEval w a := by
  have h := F.lieTreeEval_sub_mem v w d hv hw hvw a
  rw [hd, hr, F.terminal, Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem horizontalTreeValue_mk (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r) (v : ∀ i, F.layer (d i) 1) :
    F.horizontalTreeValue d a (fun i => F.higherHorizontalMk (d i) (v i)) =
      lieTreeEval (fun i => (v i).val) a := by
  apply F.top_lieTreeEval_congr _ _ d
    (fun i => (F.higherHorizontalRepresentative (d i) (F.higherHorizontalMk (d i) (v i))).property)
    (fun i => (v i).property) _ a hd hr
  intro i
  exact (F.higherHorizontalMk_eq (d i) _ _).mp (F.higherHorizontalMk_representative _ _)

theorem horizontalTreeValue_zero_of_leaf (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, F.HigherHorizontal (d i)) {i : I} (hi : i ∈ lieTreeSupport a)
    (hv : v i = 0) : F.horizontalTreeValue d a v = 0 := by
  apply lieTreeEval_eq_zero_of_leaf _ a hi
  simp only [hv, higherHorizontalRepresentative_zero, ZeroMemClass.coe_zero]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}

theorem raiseStep_layer (F : NilpotentLieFiltration L s) (hst : s ≤ t) (i : ℕ) :
    (F.raiseStep hst).layer i = F.layer i := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DegreeRankBCH
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem subgroup_le_associatedDegree (d i : ℕ) : F.subgroup d i ≤ F.associatedDegree.subgroup d :=
  fun _ hx => F.layer_le_associatedDegree d i hx

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def realQuotientPolynomialOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.realification.PolynomialOrbit w) : (F.quotientLie I hI).realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap q.log)
    (F.realification.adapted_map (F.quotientLie I hI).realification _
      (fun _ _ hx => F.realQuotientStep_mem_layer I hI hx) w q.adapted)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialSymbolMap_translate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (h : σ → ℚ) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w
      ⟨translate h (p : VectorPolynomial σ ℚ L),
        (F.mem_adaptedSubmodule w _).mpr (F.adapted_translate w hw h
          ((F.mem_adaptedSubmodule w _).mp p.property))⟩ =
      F.polynomialSymbolMap w p := by
  apply (F.polynomialSymbolMap_eq_iff w _ p).mpr
  exact F.translate_sub_coefficient_mem w hw h ((F.mem_adaptedSubmodule w _).mp p.property)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_gradedRefiltrationLayer_iff (j : ℕ) (v : F.layer j) :
    (v : L) ∈ F.gradedRefiltrationLayer U j ↔ F.associatedGradedPieceMap j v ∈ U := by
  rw [F.mem_gradedRefiltrationLayer]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨v.property, h⟩⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareRelativeLayer (j : ℕ) (hj : 1 ≤ j) :
    F.layer (j + 1) →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, 0), (F.mem_squareLieSubalgebra _).mpr (by
    simpa only [sub_zero] using F.antitone (Nat.add_le_add_right hj 1) x.property)⟩,
    F.antitone (Nat.le_succ j) x.property, (F.layer j).zero_mem, by
      change (x : L) - 0 ∈ F.layer (j + 1)
      simpa only [sub_zero] using x.property⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem mem_symbolPointwiseSubalgebra_iff (U : LieSubalgebra ℚ F.AssociatedGraded)
    (x : F.PolynomialSymbol w) :
    x ∈ F.symbolPointwiseSubalgebra b ω hlayers w U ↔
      ∀ α, coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α ∈ U := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

theorem selectedResidueSmoothPMF_projection_approximation {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (w f f₀ g₀ g : (K × I → ℤ) → ℂ) {η ε : ℝ} (hη : 0 ≤ η)
    (hw : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖w x‖ ≤ 1)
    (hf : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖f x - f₀ x‖ ≤ η)
    (hg : ∀ x ∈ rectangularWeightIndices 0 V 1, ‖g₀ x - g x‖ ≤ η)
    (hproject : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f₀ x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g₀ x)‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * f x)) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * g x)‖ ≤ 2 * η + ε := by
  have hfirst := selectedResidueSmoothPMF_approximation modulus G V hV hZ w f f₀ hη hw hf
  have hlast := selectedResidueSmoothPMF_approximation modulus G V hV hZ w g₀ g hη hw hg
  let E (a : (K × I → ℤ) → ℂ) :=
    ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * (w x * a x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E f₀) (E g)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E f₀) (E g₀) (E g)
  change ‖E f - E f₀‖ ≤ η at hfirst
  change ‖E g₀ - E g‖ ≤ η at hlast
  change ‖E f₀ - E g₀‖ ≤ ε at hproject
  change ‖E f - E g‖ ≤ 2 * η + ε
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveNormalizationError
namespace OAI

section

namespace Erdos3

theorem FiniteProbabilityWeights.norm_density_weighted_complexMean_le
    {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean (fun x => (D x : ℂ)*f x)‖ ≤ p.mean D := by
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply p.mean_mono
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hD x)]
  exact (mul_le_mul_of_nonneg_left (hf x) (hD x)).trans_eq (mul_one _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IntervalDivisorProbability
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem mean_mul_le_of_capped_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (D g φ : X → ℝ) {C ε : ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hg : ∀ x, g x ≤ C)
    (he : |p.mean (fun x => D x * φ x) - p.mean (fun x => g x * φ x)| ≤ ε) :
    p.mean (fun x => D x * φ x) ≤ C * p.mean φ + ε := by
  have hb : p.mean (fun x => g x * φ x) ≤ C * p.mean φ := by
    rw [← p.mean_const_mul]
    exact p.mean_mono (fun x => mul_le_mul_of_nonneg_right (hg x) (hφ x))
  have ht := (abs_le.mp he).2
  linarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem mean_mem_Icc (p : FiniteProbabilityWeights X) (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) : p.mean f ∈ Set.Icc a b := by
  constructor
  · exact (p.mean_const a).symm.trans_le (p.mean_mono (fun x => (hf x).1))
  · exact (p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const b)

theorem abs_mean_sub_const_le (p : FiniteProbabilityWeights X) (f : X → ℝ) (c ε : ℝ)
    (hf : ∀ x, |f x-c| ≤ ε) : |p.mean f-c| ≤ ε := by
  have h := p.mean_mem_Icc f (a := c-ε) (b := c+ε) (fun x => by
    have hx := abs_le.mp (hf x)
    constructor <;> linarith)
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem fiberLaw_complexMean {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X) (f : X → ℂ) :
    (p.fiberLaw F).complexMean f = p.complexMean (fun x => f (F x)) := by
  have h := p.complexMean_fiber_factor F (fun _ => 1) f
  simpa only [Complex.ofReal_one, one_mul, complexMean, fiberLaw_weight] using h.symm

theorem fiberLaw_mean {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X) (f : X → ℝ) :
    (p.fiberLaw F).mean f = p.mean (fun x => f (F x)) := by
  have h := congrArg Complex.re (p.fiberLaw_complexMean F (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

noncomputable def siteLaw {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) : FiniteProbabilityWeights X :=
  (p.prod (uniform T)).fiberLaw (fun z => F z.1 z.2)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HorizontalAmbientQuotient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective (F.higherHorizontalAmbient d) := by
  intro x y h
  obtain ⟨x, rfl⟩ := F.higherHorizontalMk_surjective d x
  obtain ⟨y, rfl⟩ := F.higherHorizontalMk_surjective d y
  apply (F.higherHorizontalMk_eq d x y).mpr
  exact (Submodule.Quotient.eq (F.layer d 2)).mp h

theorem real_higherHorizontalAmbient_injective (d : ℕ) :
    Function.Injective ((F.higherHorizontalAmbient d).baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ)
    (F.higherHorizontalAmbient d) (F.higherHorizontalAmbient_injective d)

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open scoped NNReal

variable {N : ℕ} [NeZero N]

noncomputable def approximationLipBound (B : Set N) (rho : ℝ≥0) : ℝ≥0 :=
  ((B.rank : ℝ≥0) * (B.approximationWidth rho)⁻¹) * CircleFourier.characterLipConstant

end Erdos3.CyclicBohr.Set

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SamplingRankProjectedContainment
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

open scoped TensorProduct

theorem integerRowPolynomial_totalDegree_le {I J : Type*} [Fintype J]
    (a : J → ℤ) {p : VectorPolynomial I ℝ (J → ℝ)} {h : ℕ}
    (hp : DegreeLE (fun _ => 1) h p) : (integerRowPolynomial a p).totalDegree ≤ h := by
  have hw : (integerRowPolynomial a p).weightedTotalDegree (1 : I → ℕ) ≤ h := by
    apply (scalar_weightedDegree_le_iff _ _ _).mpr
    intro α hα
    simp only [integerRowPolynomial, coeff_coordinate, hp α hα, map_zero]
  simpa only [MvPolynomial.weightedTotalDegree_one] using hw

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AlgebraicMajorWeightedAffineTopPullback
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators TensorProduct

variable {U R : Type*} [CommRing R]

theorem residueAffinePolynomial_eq_dilation_translate (q : ℕ) (r : U → ℤ)
    (P : MvPolynomial U ℝ) :
    residueAffinePolynomial q r P =
      aeval (fun i => C (q : ℝ) * X i) (polynomialTranslate (fun i => (r i : ℝ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [residueAffinePolynomial]
  | add P Q hP hQ =>
    simpa only [residueAffinePolynomial, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [residueAffinePolynomial, map_mul, eval₂Hom_X', polynomialTranslate_X,
      map_add, aeval_X, aeval_C, algebraMap_eq] at *
    rw [hP, add_comm (C (r i : ℝ))]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LayerSamplingRankAffine
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

noncomputable def residueAffine {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (r : I → ℤ) : VectorPolynomial I ℝ V →ₗ[ℝ] VectorPolynomial I ℝ V :=
  substitute (fun i => MvPolynomial.C (r i : ℝ) +
    MvPolynomial.C (q : ℝ) * MvPolynomial.X i)

theorem eval_residueAffine {I V : Type*} [AddCommGroup V] [Module ℝ V]
    (q : ℕ) (r : I → ℤ) (x : I → ℝ) (P : VectorPolynomial I ℝ V) :
    eval x (residueAffine q r P) = eval (fun i => (r i : ℝ) + (q : ℝ)*x i) P := by
  simp only [residueAffine, eval_substitute, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem integerRowPolynomial_residueAffine {I J : Type*} [Fintype J]
    (a : J → ℤ) (q : ℕ) (r : I → ℤ) (P : VectorPolynomial I ℝ (J → ℝ)) :
    integerRowPolynomial a (residueAffine q r P) =
      residueAffinePolynomial q r (integerRowPolynomial a P) := by
  apply MvPolynomial.funext
  intro x
  rw [integerRowPolynomial_eval, eval_residueAffine,
    residueAffinePolynomial_eval_real, integerRowPolynomial_eval]

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformCommutingCircleDecomposition
namespace OAI

section

namespace Erdos3.CircleFourier

open scoped BigOperators NNReal

variable {X ι : Type*} [PseudoMetricSpace X] [Fintype ι]

theorem exists_uniform_controlled_commuting_circle_operators
    (A : ι → IsometricCircleAction X) (hcomm : ∀ i j, (A i).Commutes (A j))
    (D : ℝ≥0)
    (horbit : ∀ i (t : Circle) x, dist ((A i).act t x) x ≤ D * ‖t‖)
    (δ p : ℝ) (hδ : 0 < δ) (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hDp : (D : ℝ) ≤ Real.exp p) (hδp : δ⁻¹ ≤ Real.exp p) :
    ∃ (J : Type) (inst : Fintype J), letI := inst
    ∃ (ν : J → ι → ℤ) (V : J → (X → ℂ) → X → ℂ),
      (Fintype.card J : ℝ) ≤ Real.exp (2 * p * (2 * p + 2) ^ 4) ∧
      (∀ j i, (|ν j i| : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4)) ∧
      (∀ j (f g : X → ℂ) (K H : ℝ≥0), LipschitzWith K f → LipschitzWith H g →
        ∀ ε : ℝ, (∀ x, ‖f x - g x‖ ≤ ε) → ∀ x, ‖V j f x - V j g x‖ ≤ ε) ∧
      ∀ (f : X → ℂ) (L B : ℝ≥0), LipschitzWith L f → (∀ x, ‖f x‖ ≤ B) →
        (L : ℝ) ≤ Real.exp p →
          (∀ j, LipschitzWith L (V j f) ∧ (∀ x, ‖V j f x‖ ≤ B)) ∧
          (∀ j i (t : Circle) x, V j f ((A i).act t x) = character (ν j i • t) * V j f x) ∧
          (∀ (g : X → X) (z : ℂ),
            (∀ i t x, (A i).act t (g x) = g ((A i).act t x)) →
            (∀ x, f (g x) = z * f x) → ∀ j x, V j f (g x) = z * V j f x) ∧
          ∀ x, ‖(∑ j, V j f x) - f x‖ ≤ δ := by
  classical
  let is := (Finset.univ : Finset ι).toList
  have hd' : (is.length : ℝ) ≤ p := by simpa [is] using hd
  let O : ℝ := Real.exp p * D
  have hO : 0 ≤ O := mul_nonneg (Real.exp_nonneg _) D.coe_nonneg
  let ε := δ / (is.length + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hOp : O ≤ Real.exp (2 * p) := by
    calc
      O ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_left hDp (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hεp : ε⁻¹ ≤ Real.exp (2 * p) := by
    have hlen : (is.length : ℝ) + 1 ≤ Real.exp p :=
      (by linarith : (is.length : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
    calc
      ε⁻¹ = ((is.length : ℝ) + 1) * δ⁻¹ := by dsimp [ε]; rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hlen hδp (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨N, hN, hcut, hNb⟩ := exists_fejer_cutoff hO hε
  have hNe : (N : ℝ) ≤ Real.exp ((2 * p + 2) ^ 4) :=
    hNb.trans (fejer_cutoff_bound (by linarith : 0 ≤ 2 * p) hO hε hOp hεp)
  have hcard : (Fintype.card (Fin is.length → FejerChoice N) : ℝ) ≤
      Real.exp (2 * p * (2 * p + 2) ^ 4) := by
    apply (Nat.cast_le.mpr (card_fejerChoices N is.length)).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg N) hNe _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul, Nat.cast_ofNat]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd' (by norm_num)) (by positivity))
  have hcover : ∀ i : ι, ∃ r : Fin is.length, is.get r = i := by
    intro i
    apply List.mem_iff_get.mp
    simp [is]
  choose index hindex using hcover
  let J := Fin is.length → FejerChoice N
  let ν : J → ι → ℤ := fun k i => -(k (index i) : ℤ)
  let V : J → (X → ℂ) → X → ℂ := fun k f =>
    iteratedCircleComponent N A is (fun r => (k r : ℤ)) f
  refine ⟨J, inferInstance, ν, V, hcard, ?_, ?_, ?_⟩
  · intro k i
    have hk : (|(k (index i) : ℤ)| : ℝ) < N := by
      exact_mod_cast abs_lt_of_mem_fejerFrequencies (k (index i)).property
    simpa only [ν, Int.cast_neg, abs_neg] using hk.le.trans hNe
  · intro k f g K H hf hg ε hfg x
    exact iteratedCircleComponent_norm_sub_le hN A is (fun r => (k r : ℤ)) hf hg hfg x
  · intro f L B hf hb hLp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k
      exact ⟨iteratedCircleComponent_lipschitz hN A is _ hf,
        iteratedCircleComponent_norm_le hN A is _ hb⟩
    · intro k i t x
      have hi := iteratedCircleComponent_character N A is (fun r => (k r : ℤ))
        (fun a _ b _ => hcomm a b) f (index i) t x
      rw [hindex i] at hi
      exact hi
    · intro g z hg hfz k x
      exact iteratedCircleComponent_equivariant N A is (fun r => (k r : ℤ))
        g z (fun i _ => hg i) hfz x
    · intro x
      change ‖(∑ k : Fin is.length → FejerChoice N,
        iteratedCircleComponent N A is (fun r => (k r : ℤ)) f x) - f x‖ ≤ δ
      rw [← iteratedCircleSmooth_eq_sum hN A is hf x]
      have hstep : ∀ i ∈ is, ∀ g : X → ℂ, LipschitzWith L g → ∀ y,
          ‖(A i).smooth N g y - g y‖ ≤ ε := by
        intro i _ g hg y
        have hη : 0 < ε / (2 * (O + 1)) := by positivity
        apply ((A i).smooth_error hN hg.continuous hO hη ?_ y).trans
          (fejer_error_le_of_cutoff hO hε hN hcut)
        intro t z
        rw [← dist_eq_norm]
        calc
          dist (g ((A i).act t z)) (g z) ≤ L * dist ((A i).act t z) z := hg.dist_le_mul _ _
          _ ≤ L * (D * ‖t‖) := mul_le_mul_of_nonneg_left (horbit i t z) L.coe_nonneg
          _ ≤ Real.exp p * (D * ‖t‖) :=
            mul_le_mul_of_nonneg_right hLp (mul_nonneg D.coe_nonneg (norm_nonneg _))
          _ = O * ‖t‖ := by dsimp [O]; ring
      apply (iteratedCircleSmooth_error hN A is hf hstep x).trans
      change (is.length : ℝ) * (δ / (is.length + 1)) ≤ δ
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

end Erdos3.CircleFourier

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScalarDominatedSlack
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace FiniteProbabilityWeights

theorem mean_comm {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (F : X → Y → ℝ) :
    p.mean (fun x => q.mean (F x)) = q.mean (fun y => p.mean (fun x => F x y)) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem mean_sum {X J : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (s : Finset J) (F : J → X → ℝ) :
    p.mean (fun x => ∑ j ∈ s, F j x) = ∑ j ∈ s, p.mean (F j) := by
  unfold mean
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_sub {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) (f g : X → ℝ) :
    p.mean (fun x => f x - g x) = p.mean f - p.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem exists_code_fiber_mass {Ω I : Type*} [Fintype Ω] [Fintype I] [Nonempty I]
    (p : FiniteProbabilityWeights Ω) (Q : Finset Ω) (code : Ω → I) :
    ∃ i, p.mass Q / Fintype.card I ≤ p.mass (Q.filter (fun x => code x = i)) := by
  have hsum : (∑ i, p.mass (Q.filter (fun x => code x = i))) = p.mass Q := by
    simp only [mass, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  have hmean : (𝔼 i, p.mass (Q.filter (fun x => code x = i))) = p.mass Q / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card, hsum]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean.ge
  exact ⟨i, hi⟩

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedProductDensity
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)

theorem mean_mono_on_support {f g : Ω → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x ≤ g x) : p.mean f ≤ p.mean g := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp [hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)

theorem abs_mean_le_mean_abs (f : Ω → ℝ) : |p.mean f| ≤ p.mean (fun x => |f x|) := by
  unfold mean
  calc
    _ ≤ ∑ x, |p.weight x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]

theorem abs_mean_le_on_support (f : Ω → ℝ) {C : ℝ}
    (hf : ∀ x, p.weight x ≠ 0 → |f x| ≤ C) : |p.mean f| ≤ C := by
  exact (p.abs_mean_le_mean_abs f).trans
    ((p.mean_mono_on_support hf).trans_eq (p.mean_const C))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def finiteWeightDensity (p : FiniteProbabilityWeights Ω) (w : Ω → ℝ)
    (x : Ω) : ℝ := w x / p.weight x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def observedProductDensity {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))
    (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i) (f : Ω → ℝ) : (∀ i, X i) → ℝ :=
  finiteWeightDensity (FiniteProbabilityWeights.pi μ) (fun y => p.fiberMean F y f)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneSiteWeightIdentity
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem layeredSiteWeight_oneSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (φ : (I → ℝ) → ℂ)
    (b : Option K → I → ℝ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s) (fun _ => φ) b =
      φ (integerSiteValue (affineSite root difference ∅) b) := by
  simp only [layeredSiteWeight, map_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul]
  exact Fintype.prod_subsingleton
    (fun s : Finset (Fin 0) => φ (integerSiteValue (affineSite root difference s) b))
    (∅ : Finset (Fin 0))

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineOneSiteNormalizedLaw
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem layeredSiteWeight_physical {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (φ : (I → ℝ) → ℂ)
    (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s) (fun _ => φ)
      (fun k j => (z (k,j) : ℝ)) = φ (physicalAffineSite root z) := by
  rw [layeredSiteWeight_oneSite, integerSiteValue_oneSite]

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteCenteredKernel
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

noncomputable def joint (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y) :
    FiniteProbabilityWeights (X × Y) where
  weight z := p.weight z.1 * (q z.1).weight z.2
  nonneg z := mul_nonneg (p.nonneg z.1) ((q z.1).nonneg z.2)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, total, mul_one]

theorem joint_mean (p : FiniteProbabilityWeights X) (q : X → FiniteProbabilityWeights Y)
    (f : X × Y → ℝ) :
    (p.joint q).mean f = p.mean (fun x => (q x).mean (fun y => f (x,y))) := by
  simp only [mean, joint, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productSectionAverage (T A : Finset I) (z : ∀ i, X i)
    (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (FiniteProbabilityWeights.pi μ).mean
    (fun y => f (productCoordinateMix T (productCoordinateMix A z y) x))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationCost
namespace OAI

section

namespace Erdos3.MultilinearityBudget

open scoped TensorProduct NNReal

noncomputable def reconstructionExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_rationalReconstructionLipschitzBound_exp s)

theorem reconstructionExponent_control (s d n H : ℕ) (A B : ℝ≥0) (p : ℝ)
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hA : (A : ℝ) ≤ Real.exp p) (hB : (B : ℝ) ≤ Real.exp p) :
    (rationalReconstructionLipschitzBound s d n H A B : ℝ) ≤
      Real.exp ((p + reconstructionExponent s) ^ reconstructionExponent s) :=
  (Classical.choose_spec (exists_rationalReconstructionLipschitzBound_exp s)).2 d n H A B p
    hp hd hn hH hA hB

end Erdos3.MultilinearityBudget

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_pos (p : FiniteProbabilityWeights Ω) : ∃ x, 0 < p.weight x := by
  by_contra h
  push Not at h
  have hs : (∑ x, p.weight x) ≤ 0 := Finset.sum_nonpos (fun x _ => h x)
  rw [p.total] at hs
  norm_num at hs

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem complexMean_div (p : FiniteProbabilityWeights X) (f : X → ℂ) (z : ℂ) :
    p.complexMean (fun x => f x / z) = p.complexMean f / z := by
  simp only [complexMean, mul_div_assoc, Finset.sum_div]

theorem exists_positive_weight_ge_mean (p : FiniteProbabilityWeights X) (f : X → ℝ) :
    ∃ x, 0 < p.weight x ∧ p.mean f ≤ f x := by
  let A := Finset.univ.filter (fun x => 0 < p.weight x)
  have hA : A.Nonempty := by
    obtain ⟨x, hx⟩ := p.exists_weight_pos
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image f hA
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  calc
    p.mean f ≤ p.mean (fun _ => f x) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : 0 < p.weight y
      · exact mul_le_mul_of_nonneg_left
          (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)) hy.le
      · have hz : p.weight y = 0 := le_antisymm (le_of_not_gt hy) (p.nonneg y)
        simp only [hz, zero_mul, le_refl]
    _ = f x := p.mean_const _

theorem exists_positive_weight_ge_complexMean_re (p : FiniteProbabilityWeights X) (f : X → ℂ) :
    ∃ x, 0 < p.weight x ∧ (p.complexMean f).re ≤ (f x).re := by
  rw [p.complexMean_re]
  exact p.exists_positive_weight_ge_mean _

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LocalBohrAlmostPeriodsRelative
namespace OAI

section

namespace Erdos3.CyclicBohr.Set

open _root_.Finset
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

noncomputable def characterBasis (Delta : Finset (AddChar (ZMod N) ℂ))
    (r : ℝ≥0) : Set N :=
  ofFrequencies (Delta.map AddChar.zmodAddEquiv.symm.toEmbedding) r r.coe_nonneg

@[simp] theorem rank_characterBasis (Delta : Finset (AddChar (ZMod N) ℂ)) (r : ℝ≥0) :
    (characterBasis Delta r).rank = Delta.card := by
  simp [characterBasis]

@[simp] theorem radius_characterBasis (Delta : Finset (AddChar (ZMod N) ℂ)) (r : ℝ≥0) :
    (characterBasis Delta r).radius = r := rfl

theorem norm_one_sub_le_of_mem_characterBasis
    {Delta : Finset (AddChar (ZMod N) ℂ)} {r : ℝ≥0} {x : ZMod N}
    (hx : x ∈ characterBasis Delta r) {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Delta) :
    ‖1 - psi x‖ ≤ r := by
  have hmem : AddChar.zmodAddEquiv.symm psi ∈
      Delta.map AddChar.zmodAddEquiv.symm.toEmbedding :=
    Finset.mem_map.mpr ⟨psi, hpsi, rfl⟩
  have h := mem_iff.mp hx _ hmem
  simpa only [characterBasis, radius_ofFrequencies, character,
    AddEquiv.apply_symm_apply] using h

theorem norm_one_sub_le_of_mem_characterBasis_addSpan
    {Delta : Finset (AddChar (ZMod N) ℂ)} {r : ℝ≥0} {x : ZMod N}
    (hx : x ∈ characterBasis Delta r) {psi : AddChar (ZMod N) ℂ}
    (hpsi : psi ∈ Delta.addSpan) :
    ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r := by
  obtain ⟨epsilon, hepsilon, hsum⟩ := Finset.mem_addSpan.mp hpsi
  rw [← hsum, AddChar.sum_apply]
  calc
    ‖1 - ∏ gamma ∈ Delta, (epsilon gamma • gamma) x‖ ≤
        ∑ gamma ∈ Delta, ‖1 - (epsilon gamma • gamma) x‖ :=
      norm_one_sub_prod_le_sum Delta _ (fun gamma _ => by simp)
    _ ≤ ∑ _gamma ∈ Delta, (r : ℝ) := by
      apply Finset.sum_le_sum
      intro gamma hgamma
      have h := norm_one_sub_le_of_mem_characterBasis hx hgamma
      rcases hepsilon gamma with hneg | hzero | hone
      · rw [hneg, neg_one_zsmul, AddChar.neg_apply, AddChar.map_neg_eq_conj]
        have heq : ‖1 - (starRingEnd ℂ) (gamma x)‖ = ‖1 - gamma x‖ := by
          simpa using (RCLike.norm_conj (1 - gamma x))
        rwa [heq]
      · simp [hzero]
      · simpa [hone] using h
    _ = (Delta.card : ℝ) * r := by simp

noncomputable def adjoinCharacters (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) : Set N :=
  (B.ndilate sigma).meet (characterBasis Delta r)

theorem rank_adjoinCharacters_le (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).rank ≤ B.rank + Delta.card := by
  simpa only [adjoinCharacters, rank_ndilate, rank_characterBasis] using
    rank_meet_le (B.ndilate sigma) (characterBasis Delta r)

@[simp] theorem radius_adjoinCharacters (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).radius = min ((sigma : ℝ) * B.radius) r := by
  simp only [adjoinCharacters, radius_meet, radius_ndilate, radius_characterBasis]

theorem adjoinCharacters_subset_ndilate (B : Set N)
    (Delta : Finset (AddChar (ZMod N) ℂ)) (sigma r : ℝ≥0) :
    (adjoinCharacters B Delta sigma r).carrier ⊆ (B.ndilate sigma).carrier :=
  carrier_meet_subset_left _ _

theorem norm_one_sub_le_of_relative_cover
    (B : Set N) (hBreg : B.IsRankRegular)
    {Delta Q : Finset (AddChar (ZMod N) ℂ)} {sigma r : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum B.carrier (1 / 2), psi = z + s)
    {x : ZMod N} (hx : x ∈ adjoinCharacters B Delta sigma r)
    {psi : AddChar (ZMod N) ℂ} (hpsi : psi ∈ Q) :
    ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r +
      800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  obtain ⟨z, hz, s, hs, rfl⟩ := hcover psi hpsi
  have hxB := adjoinCharacters_subset_ndilate B Delta sigma r hx
  have hxDelta : x ∈ characterBasis Delta r :=
    carrier_meet_subset_right (B.ndilate sigma) (characterBasis Delta r) hx
  have hzbound := norm_one_sub_le_of_mem_characterBasis_addSpan hxDelta hz
  have hsbound := Erdos3.norm_one_sub_le_of_mem_largeSpectrum_half hBreg hsigma hs hxB
  rw [AddChar.add_apply]
  exact (norm_one_sub_mul_of_norm_le_one (by simp)).trans (add_le_add hzbound hsbound)

theorem exists_regular_bohr_of_relative_cover
    (B : Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {Delta Q : Finset (AddChar (ZMod N) ℂ)} {sigma r : ℝ≥0}
    (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum B.carrier (1 / 2), psi = z + s) :
    ∃ R : Set N, R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
      min ((sigma : ℝ) * B.radius) r / 2 ≤ R.radius ∧
      R.radius ≤ min ((sigma : ℝ) * B.radius) r ∧
      R.carrier ⊆ (B.ndilate sigma).carrier ∧
      ∀ x ∈ R.carrier, ∀ psi ∈ Q,
        ‖1 - psi x‖ ≤ (Delta.card : ℝ) * r +
          800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  let D := adjoinCharacters B Delta sigma r
  have hDpos : 0 < D.radius := by
    rw [radius_adjoinCharacters]
    exact lt_min (mul_pos (by exact_mod_cast hsigma0) hBpos) (by exact_mod_cast hr0)
  obtain ⟨R, hfreq, hRreg, hlo, hhi, hsub, _⟩ :=
    exists_controlled_regular_subdilate D hDpos 1 (by norm_num) le_rfl
  have hRD : R.carrier ⊆ D.carrier := by simpa only [ndilate_one] using hsub
  have hrank : R.rank = D.rank := congrArg Finset.card hfreq
  refine ⟨R, hRreg, hrank.le.trans (rank_adjoinCharacters_le B Delta sigma r), ?_, ?_,
    hRD.trans (adjoinCharacters_subset_ndilate B Delta sigma r), ?_⟩
  · simpa only [NNReal.coe_one, one_mul, D, radius_adjoinCharacters] using hlo
  · simpa only [NNReal.coe_one, one_mul, D, radius_adjoinCharacters] using hhi
  · intro x hx psi hpsi
    exact norm_one_sub_le_of_relative_cover B hBreg hsigma hcover (hRD hx) hpsi

end Erdos3.CyclicBohr.Set

end

section

namespace Erdos3.RelativeChangSanders

open scoped NNReal

variable {N : ℕ} [NeZero N]

theorem localChangBaseScale_pos (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) :
    0 < localChangBaseScale B X eta := by
  unfold localChangBaseScale
  positivity

theorem exists_regular_relative_spectrum_controller
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    (X : Finset (ZMod N)) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) (sigma r : ℝ≥0)
    (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    ∃ rho : ℝ≥0, ∃ C : CyclicBohr.Set N,
      ∃ Delta : Finset (AddChar (ZMod N) ℂ), ∃ R : CyclicBohr.Set N,
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.ndilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
        min ((sigma : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius / 2)) r / 2 ≤
          R.radius ∧
        R.radius ≤ min ((sigma : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius)) r ∧
        R.carrier ⊆ (C.ndilate sigma).carrier ∧
        ∀ x ∈ R.carrier, ∀ psi ∈ Chang.largeSpectrum X eta,
          ‖1 - psi x‖ ≤ localChangDimension B X eta * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by
  obtain ⟨rho, C, Delta, hrho0, hrho1, hC, hCreg, hcard, hDelta, hcover⟩ :=
    exists_relativeLargeSpectrum_cover B hBpos hBreg X hX hXB eta heta
  have hCrank : C.rank = B.rank := by simp [hC]
  have hrho0R : (1 / 2 : ℝ) ≤ rho := by exact_mod_cast hrho0
  have hrho1R : (rho : ℝ) ≤ 1 := by exact_mod_cast hrho1
  have ha : (0 : ℝ) < localChangBaseScale B X eta := by
    exact_mod_cast localChangBaseScale_pos B X eta
  have hCradius : C.radius = (rho : ℝ) * ((localChangBaseScale B X eta : ℝ) * B.radius) := by
    simp only [hC, CyclicBohr.Set.radius_ndilate, NNReal.coe_mul, mul_assoc]
  have hCpos : 0 < C.radius := by
    rw [hCradius]
    exact mul_pos (by linarith) (mul_pos ha hBpos)
  have hClo : (localChangBaseScale B X eta : ℝ) * B.radius / 2 ≤ C.radius := by
    rw [hCradius]
    nlinarith [mul_nonneg ha.le hBpos.le]
  have hChi : C.radius ≤ (localChangBaseScale B X eta : ℝ) * B.radius := by
    rw [hCradius]
    nlinarith [mul_nonneg ha.le hBpos.le]
  have hsigmaC : sigma ≤ 1 / (100 * (2 * max C.rank 1 : ℕ) : ℝ≥0) := by
    simpa only [hCrank] using hsigma
  obtain ⟨R, hRreg, hRrank, hRlo, hRhi, hRsub, hRphase⟩ :=
    CyclicBohr.Set.exists_regular_bohr_of_relative_cover
      C hCpos hCreg hsigma0 hr0 hsigmaC hcover
  refine ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta, hRreg,
    ?_, ?_, ?_, hRsub, ?_⟩
  · simpa only [hCrank] using hRrank
  · apply le_trans _ hRlo
    exact div_le_div_of_nonneg_right
      (min_le_min_right (r : ℝ) (mul_le_mul_of_nonneg_left hClo sigma.coe_nonneg))
      (by norm_num)
  · apply hRhi.trans
    exact min_le_min_right (r : ℝ) (mul_le_mul_of_nonneg_left hChi sigma.coe_nonneg)
  · intro x hx psi hpsi
    have hphase := hRphase x hx psi hpsi
    rw [hCrank] at hphase
    exact hphase.trans (add_le_add
      (mul_le_mul_of_nonneg_right hcard r.coe_nonneg) le_rfl)

end Erdos3.RelativeChangSanders

end

section

namespace Erdos3

open scoped BigOperators NNReal Pointwise

variable {N : ℕ} [NeZero N]

namespace RelativeChangSanders

theorem localChangBaseScale_le_one
    (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) :
    localChangBaseScale B X eta ≤ 1 := by
  have hd : (1 : ℝ≥0) ≤ (2 * max B.rank 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * max B.rank 1 by omega)
  have hk : (1 : ℝ≥0) ≤ (2 * localChangCap B X eta + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ 2 * localChangCap B X eta + 1 by omega)
  unfold localChangBaseScale
  rw [← one_div, div_le_one (by positivity)]
  nlinarith

end RelativeChangSanders

end Erdos3

end

section

namespace Erdos3.CyclicCrootSisask

open scoped BigOperators NNReal Pointwise
open RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem exists_local_bohr_triple_almostPeriods_relative
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A S L : Finset (ZMod N)} (hA : A.Nonempty) (hS : S.Nonempty) (hL : L.Nonempty)
    (hSB : S ⊆ B.carrier) (M : Finset (ZMod N))
    (q : ℕ) (hq : 0 < q) {delta : ℝ} (hdelta : 0 < delta)
    (sigma r : ℝ≥0) (hsigma0 : 0 < sigma) (hr0 : 0 < r)
    (hsigma : sigma ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0)) :
    let m := convolutionMomentOrder M L
    let k := crootSisaskSampleSize m ((delta / q) / Real.exp 1)
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ (T : Finset (ZMod N)) (R : CyclicBohr.Set N),
      T.Nonempty ∧ T ⊆ S ∧
      (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card) ∧
      R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + localChangDimension B T (1 / 2) ∧
      min ((sigma : ℝ) * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2 ≤
        R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧
      ∀ t ∈ R.carrier, ∀ x,
        |u (x + t) - u x| ≤ 2 * delta +
          (localChangDimension B T (1 / 2) * r +
            800 * ((max B.rank 1 : ℕ) : ℝ) * sigma + 2 * (1 / 2 : ℝ) ^ q) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  intro m k u
  obtain ⟨T, X, z, hTS, hz, hXeq, hzero, hXS, hcount, happrox⟩ :=
    exists_local_boosted_triple_almostPeriods hA hS hL M q hq hdelta
  have hX : X.Nonempty := ⟨0, hzero⟩
  have hT : T.Nonempty := ⟨z, hz⟩
  obtain ⟨rho, C, Delta, R, hrho0, hrho1, hC, hCreg, hcard, hDelta,
      hRreg, hRrank, hRwidth, hRupper, hRsub, hphase⟩ :=
    exists_regular_relative_spectrum_controller B hBpos hBreg T hT (hTS.trans hSB)
      (1 / 2) (by norm_num) sigma r hsigma0 hr0 hsigma
  have hsigma1 : sigma ≤ 1 := by
    apply hsigma.trans
    rw [div_le_one (by positivity)]
    exact_mod_cast (show 1 ≤ 100 * (2 * max B.rank 1) by omega)
  have ha1 := localChangBaseScale_le_one B T (1 / 2)
  have hscale : sigma * (rho * localChangBaseScale B T (1 / 2)) ≤ 1 := by
    calc
      sigma * (rho * localChangBaseScale B T (1 / 2)) ≤ 1 * (1 * 1) :=
        mul_le_mul hsigma1 (mul_le_mul hrho1 ha1 (by positivity) (by norm_num))
          (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hCB : (C.ndilate sigma).carrier ⊆ B.carrier := by
    rw [hC, CyclicBohr.Set.ndilate_ndilate]
    simpa only [CyclicBohr.Set.ndilate_one] using
      CyclicBohr.Set.carrier_ndilate_mono (B := B) hscale
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) :=
    (Nat.cast_nonneg Delta.card).trans hcard
  refine ⟨T, R, hT, hTS, hcount, hRreg, ?_, hRwidth,
    hRupper.trans (min_le_right _ _), hRsub.trans hCB, ?_⟩
  · have hRrankR : (R.rank : ℝ) ≤ B.rank + Delta.card := by exact_mod_cast hRrank
    exact hRrankR.trans (add_le_add le_rfl hcard)
  · intro t ht x
    have htheta : 0 ≤ localChangDimension B T (1 / 2) * (r : ℝ) +
        800 * ((max B.rank 1 : ℕ) : ℝ) * sigma := by positivity
    have h := triple_translate_le_of_iterated_approx hA hL hX M q
      (eta := (1 / 2 : ℝ)) (by norm_num) htheta t (x + t) happrox
      (fun psi hpsi => hphase t ht psi (by
        rw [hXeq] at hpsi
        exact (Chang.mem_largeSpectrum_map_subRight_iff T z (1 / 2) psi).1 hpsi))
    simpa only [add_sub_cancel_right, abs_sub_comm] using h

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LocalSpectrumBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal Pointwise

namespace RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem localChangDimension_half_le_of_card
    (B : CyclicBohr.Set N) {T : Finset (ZMod N)} (hT : T.Nonempty)
    {K : ℝ} (hK : 0 < K) (k : ℕ)
    (hcount : (B.carrier.card : ℝ) / (2 * K ^ k) ≤ T.card) :
    localChangDimension B T (1 / 2) ≤ 8 * (1 + Real.log 4 + k * Real.log K) := by
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hBpos : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  have hden : 0 < 2 * K ^ k := by positivity
  have hprod := (div_le_iff₀ hden).mp hcount
  have hratio : 2 * (B.carrier.card : ℝ) / T.card ≤ 4 * K ^ k := by
    rw [div_le_iff₀ hTpos]
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * (B.carrier.card : ℝ) / T.card) hratio
  rw [Real.log_mul (by norm_num) (pow_ne_zero k hK.ne'), Real.log_pow] at hlog
  unfold localChangDimension
  norm_num
  linarith

theorem localChangBaseScale_ge_of_dimension_le
    (B : CyclicBohr.Set N) (T : Finset (ZMod N)) (eta D : ℝ)
    (hD : localChangDimension B T eta ≤ D) :
    (100 * ((2 * max B.rank 1 : ℕ) : ℝ≥0) *
      ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹ ≤ localChangBaseScale B T eta := by
  have hcap : localChangCap B T eta ≤ ⌈D⌉₊ + 1 :=
    Nat.add_le_add_right (Nat.ceil_mono hD) 1
  have hcap' : ((2 * localChangCap B T eta + 1 : ℕ) : ℝ≥0) ≤
      ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcap) 1
  unfold localChangBaseScale
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hcap' (by positivity))

end RelativeChangSanders
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.QuarticSamplingBudget
namespace OAI

section

namespace Erdos3.RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem local_dimension_le_quartic_of_cubic_sampling
    (B : CyclicBohr.Set N) {T : Finset (ZMod N)} (hT : T.Nonempty)
    {p C : ℝ} (hp : 0 ≤ p) (_hC : 0 ≤ C) (k : ℕ)
    (hk : (k : ℝ) ≤ C * (p + 1) ^ 3)
    (hcount : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card) :
    localChangDimension B T (1 / 2) ≤ 8 * (1 + Real.log 4 + C) * (p + 1) ^ 4 := by
  have hdim := localChangDimension_half_le_of_card B hT
    (by positivity : 0 < 2 * Real.exp p) k hcount
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogK : Real.log (2 * Real.exp p) ≤ p + 1 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero p), Real.log_exp]
    linarith
  have hprod : (k : ℝ) * Real.log (2 * Real.exp p) ≤ C * (p + 1) ^ 4 := by
    calc
      _ ≤ (k : ℝ) * (p + 1) := mul_le_mul_of_nonneg_left hlogK (Nat.cast_nonneg _)
      _ ≤ (C * (p + 1) ^ 3) * (p + 1) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = C * (p + 1) ^ 4 := by ring
  have hp4 : 1 ≤ (p + 1) ^ 4 := one_le_pow₀ (show 1 ≤ p + 1 by linarith)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hconst : 1 + Real.log 4 ≤ (1 + Real.log 4) * (p + 1) ^ 4 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp4 (by positivity : 0 ≤ 1 + Real.log 4)
  nlinarith

end Erdos3.RelativeChangSanders

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods
namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open RelativeChangSanders
open scoped NNReal Pointwise

variable {N : ℕ} [NeZero N]

theorem exists_quartic_local_almostPeriods
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    {A L : Finset (ZMod N)} (hA : A.Nonempty) (hL : L.Nonempty) (M : Finset (ZMod N))
    {epsilon p : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hp : 0 ≤ p)
    (hratio : (M.card : ℝ) / L.card ≤ Real.exp (2 * p))
    (hdoubling : ((A + B.carrier).card : ℝ) ≤ (2 * Real.exp p) * A.card) :
    let D := rankQuarticFactor epsilon * (p + 1) ^ 4
    let d := max B.rank 1
    let a : ℝ≥0 := (100 * ((2 * d : ℕ) : ℝ≥0) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
    let sigma := epsilon * Real.exp (-p) / (6400 * (d : ℝ))
    let r := epsilon * Real.exp (-p) / (8 * (D + 1))
    let u := setAverageTranslate L (setAverageTranslate A (realSetIndicator M))
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ (R.rank : ℝ) ≤ B.rank + D ∧
      min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤ R.radius ∧
      R.radius ≤ r ∧
      R.carrier ⊆ B.carrier ∧ ∀ t ∈ R.carrier, ∀ x, |u (x + t) - u x| ≤ epsilon := by
  intro D d a sigma r u
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (rankQuarticFactor_pos epsilon).le (pow_nonneg (by positivity) _)
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  let sigmaN : ℝ≥0 := ⟨sigma, hsigma.le⟩
  let rN : ℝ≥0 := ⟨r, hr.le⟩
  have hsigreg : sigmaN ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0) := by
    have h := old_frequency_scale_le_regularity hepsilon.le hepsilon1 hp hd
    change sigma ≤ ((1 : ℝ) / (100 * ((2 * max B.rank 1 : ℕ) : ℝ)))
    dsimp [sigma, d] at h ⊢
    push_cast at h ⊢
    convert h using 1
    ring
  let q := spectralIterations epsilon p
  let k := crootSisaskSampleSize (convolutionMomentOrder M L) (((epsilon / 8) / q) / Real.exp 1)
  obtain ⟨T, R, hT, hTB, hcount, hRreg, hRrank, hRwidth, hRupper, hRB, hshift⟩ :=
    exists_local_bohr_triple_almostPeriods_relative B hBpos hBreg hA B.carrier_nonempty hL
      (fun _ h => h) M q (spectralIterations_pos epsilon p)
      (by positivity : 0 < epsilon / 8) sigmaN rN hsigma hr hsigreg
  have hcount' : (B.carrier.card : ℝ) / (2 * (2 * Real.exp p) ^ k) ≤ T.card :=
    samplingDensity_le_of_smallDoubling hA B.carrier_nonempty k (by positivity) hdoubling hcount
  have hk : (k : ℝ) ≤ samplingCubicFactor epsilon * (p + 1) ^ 3 :=
    local_sample_size_le_cubic M L hepsilon hepsilon1 hp hratio
  have hdim : localChangDimension B T (1 / 2) ≤ D :=
    local_dimension_le_quartic_of_cubic_sampling B hT hp (samplingCubicFactor_pos epsilon).le k hk hcount'
  have hdim0 : 0 ≤ localChangDimension B T (1 / 2) := by
    have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
    have hcard : (T.card : ℝ) ≤ B.carrier.card := by exact_mod_cast Finset.card_le_card hTB
    have hratio1 : 1 ≤ 2 * (B.carrier.card : ℝ) / T.card := by
      rw [le_div_iff₀ hTpos]
      linarith
    have hlog := Real.log_nonneg hratio1
    unfold localChangDimension
    positivity
  have ha : a ≤ localChangBaseScale B T (1 / 2) :=
    localChangBaseScale_ge_of_dimension_le B T (1 / 2) D hdim
  refine ⟨R, hRreg, hRrank.trans (add_le_add le_rfl hdim), ?_, hRupper, hRB, ?_⟩
  · apply le_trans _ hRwidth
    change min (sigma * ((a : ℝ) * B.radius / 2)) r / 2 ≤
      min (sigma * ((localChangBaseScale B T (1 / 2) : ℝ) * B.radius / 2)) r / 2
    gcongr
  · intro t ht x
    apply (hshift t ht x).trans
    exact chosen_scales_error_le hepsilon hd hD hdim0 hdim hratio

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise NNReal

theorem exists_quartic_bogolyubov {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ R : CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : ℝ) ≤ 1 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius ∧
      R.carrier ⊆ 2 • A - 2 • A := by
  have hApos : (0 : ℝ) < A.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast NeZero.pos N)).trans_le hdensity
  have hA : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hNle : (N : ℝ) ≤ Real.exp p * A.card := by
    calc
      (N : ℝ) = Real.exp p * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      _ ≤ Real.exp p * A.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos p).le
  have hratio : ((A - A).card : ℝ) / (-A).card ≤ Real.exp (2 * p) := by
    rw [Finset.card_neg, div_le_iff₀ hApos]
    calc
      ((A - A).card : ℝ) ≤ N := by
        exact_mod_cast (show (A - A).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ (A - A))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ Real.exp (2 * p) * A.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hApos.le
  have hdoubling : ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤
      (2 * Real.exp p) * A.card := by
    calc
      ((A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier).card ≤ N by
          simpa only [ZMod.card] using Finset.card_le_univ
            (A + (CyclicBohr.Set.whole : CyclicBohr.Set N).carrier))
      _ ≤ Real.exp p * A.card := hNle
      _ ≤ (2 * Real.exp p) * A.card := by nlinarith [Real.exp_pos p]
  obtain ⟨R, hRreg, hRrank, hRwidth, hRupper, _, hshift⟩ :=
    exists_quartic_local_almostPeriods CyclicBohr.Set.whole (by norm_num)
      CyclicBohr.Set.isRankRegular_whole hA hA.neg (A - A)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hp hratio hdoubling
  let C₀ := rankQuarticFactor (1 / 2)
  let D := C₀ * (p + 1) ^ 4
  let a : ℝ≥0 := (100 * 2 * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹
  have hC₀ : 0 < C₀ := rankQuarticFactor_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  simp only [CyclicBohr.Set.rank_whole, CyclicBohr.Set.radius_whole, max_self,
    Nat.cast_one, Nat.cast_ofNat, mul_one] at hRrank hRwidth hRupper
  change (R.rank : ℝ) ≤ 1 + D at hRrank
  change min (((1 / 2 : ℝ) * Real.exp (-p) / 6400) * ((a : ℝ) / 2))
      (((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1))) / 2 ≤ R.radius at hRwidth
  change R.radius ≤ ((1 / 2 : ℝ) * Real.exp (-p)) / (8 * (D + 1)) at hRupper
  have ha : 1 / (1000 * (1 : ℝ) * (D + 1)) ≤ (a : ℝ) := by
    simpa only [a, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast,
      NNReal.coe_ofNat, mul_one] using BohrWidthBudget.selector_scale_lower_bound
        (d := 1) (by norm_num) hD
  have hRrat : ((1 / 2 : ℝ) * Real.exp (-p)) /
      (10240000000 * (D + 1)) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_lower_bound
      (u := (1 / 2 : ℝ) * Real.exp (-p)) (d := 1) (D := D) (w := 1) (v := 1)
      (by positivity) (by norm_num) hD (by norm_num) (by norm_num) (by norm_num) ha
    apply le_trans _ hRwidth
    simpa only [one_pow, mul_one] using h
  have hC : 0 < almostPeriodicityWidthConstant (1 / 2) :=
    almostPeriodicityWidthConstant_pos (by norm_num)
  have hRexp : Real.exp (-(almostPeriodicityWidthConstant (1 / 2) *
      (1 + p + Real.log 3))) ≤ R.radius := by
    have h := BohrWidthBudget.rational_width_ge_exponential
      (epsilon := 1 / 2) (C := C₀) (p := p) (d := 1) (w := 1)
      (by norm_num) hC₀.le hp (by norm_num) (by norm_num)
    apply le_trans _ hRrat
    simpa only [almostPeriodicityWidthConstant, D, C₀, one_pow, mul_one, one_mul,
      show (2 : ℝ) + 1 = 3 by norm_num] using h
  have hlog : Real.log 3 ≤ (2 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hbudget : almostPeriodicityWidthConstant (1 / 2) * (1 + p + Real.log 3) ≤
      quarticBogolyubovConstant * (p + 1) := by
    have h := mul_le_mul_of_nonneg_left hlog hC.le
    unfold quarticBogolyubovConstant
    nlinarith [mul_nonneg hC.le hp]
  have hwidth : Real.exp (-(quarticBogolyubovConstant * (p + 1))) ≤ R.radius :=
    (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hRexp
  refine ⟨R, hRreg, (Real.exp_pos _).trans_le hwidth, ?_, ?_, hwidth, ?_⟩
  · apply hRupper.trans
    apply (div_le_one (by positivity)).mpr
    have h := Real.exp_le_one_iff.mpr (by linarith : -p ≤ 0)
    nlinarith
  · have hC₀C := rankQuarticFactor_le_widthConstant
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    have hCC : C₀ ≤ quarticBogolyubovConstant := by
      dsimp [C₀, quarticBogolyubovConstant]
      linarith
    have hh : C₀ * (p + 1) ^ 4 ≤ quarticBogolyubovConstant * (p + 1) ^ 4 :=
      mul_le_mul_of_nonneg_right hCC (by positivity)
    exact hRrank.trans (add_le_add le_rfl hh)
  · intro t ht
    have hprob : |differenceEventProbability A A (A - A) t - 1| ≤ (1 / 2 : ℝ) := by
      simpa only [← differenceEventProbability_eq_triple, zero_add,
        differenceEventProbability_self_zero A hA] using hshift t ht 0
    apply mem_fourfold_difference_of_probability_pos A t
    have h := (abs_le.mp hprob).1
    linarith

end Erdos3.CyclicCrootSisask

end

section

namespace Erdos3.CyclicCrootSisask

open scoped Pointwise

theorem exists_quartic_bogolyubov_progression {N : ℕ} [NeZero N]
    (A : Finset (ZMod N)) {p : ℝ} (hp : 0 ≤ p)
    (hdensity : Real.exp (-p) * N ≤ (A.card : ℝ)) :
    ∃ Q : BohrProgression.CyclicCenteredGAP N,
      (Q.rank : ℝ) ≤ 2 + quarticBogolyubovConstant * (p + 1) ^ 4 ∧
      Q.Proper ∧ Q.carrier ⊆ 2 • A - 2 • A ∧
      Real.exp (-(quarticBogolyubovProgressionConstant * (p + 1) ^ 8)) * N ≤
        (Q.carrier.card : ℝ) := by
  obtain ⟨B, _hreg, hB, hB1, hrank, hwidth, hsub⟩ := exists_quartic_bogolyubov A hp hdensity
  obtain ⟨Q, hr, hQ, hQB, hcard⟩ := BohrProgression.exists_proper_progression_of_quartic_bounds
    B quarticBogolyubovConstant_pos.le hp hB hB1 hrank hwidth
  exact ⟨Q, hr, hQ, hQB.trans hsub, hcard⟩

end Erdos3.CyclicCrootSisask

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ObservedSourceEquivalence
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem mean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) (e : X ≃ Y)
    (hweight : ∀ x, q.weight (e x) = p.weight x) (f : Y → ℝ) :
    p.mean (fun x => f (e x)) = q.mean f := by
  calc
    _ = ∑ x, q.weight (e x) * f (e x) := by
      unfold mean
      simp only [hweight]
    _ = _ := e.sum_comp (fun y => q.weight y * f y)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.GeneratorCells
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

namespace BooleanCutTest

omit [Fintype Ω] in
theorem eval_sq (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ^ 2 = A.eval x := by
  by_cases hx : x ∈ A <;> simp [hx]

omit [Fintype Ω] in
theorem eval_le_one (A : BooleanCutTest Ω) (x : Ω) :
    A.eval x ≤ 1 := by
  by_cases hx : x ∈ A <;> simp [hx]

end BooleanCutTest

theorem booleanCut_measurable_generatedBy (A : BooleanCutTest Ω) :
    IsPartitionMeasurable
      (FacePartition.generatedBy ({A} : Finset (Finset Ω))) A.eval := by
  intro x y hy
  have hxy : x ∈ A ↔ y ∈ A := by
    have hsignature :=
      (FacePartition.mem_part_generatedBy_iff
        ({A} : Finset (Finset Ω)) x y).1 hy
    exact hsignature A (by simp)
  by_cases hx : x ∈ A
  · have hyA : y ∈ A := hxy.mp hx
    simp [hx, hyA]
  · have hyA : y ∉ A := by
      intro hy
      exact hx (hxy.mpr hy)
    simp [hx, hyA]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

@[simp]
theorem apSimplexForm_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A)
    (j : Fin (r + 2)) :
    apSimplexForm (r + 2) N j
        (deleteCoordinate (diagonalAPSimplex r N A p) j) =
      p.1.1 := by
  rw [apSimplexForm_deleteCoordinate,
    simplexCoordinateMoment_diagonalAPSimplex,
    simplexCoordinateSum_diagonalAPSimplex]
  simp

theorem diagonalAPSimplex_mem_simplexFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    diagonalAPSimplex r N A p ∈
      (apSetHypergraph (r + 2) N A).simplexFinset := by
  let : ∀ _ : Fin (r + 2), Fintype (ZMod N) :=
    fun _ => inferInstance
  rw [SimplexHypergraph.mem_simplexFinset]
  intro j
  rw [apSetHypergraph_edge,
    apSimplexForm_diagonalAPSimplex]
  exact p.1.2

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedVectorToFinTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

namespace SimplexHypergraph

noncomputable def deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    Finset (Fin (n + 1) × (Fin n → G)) := by
  classical
  exact Finset.univ.biUnion fun j =>
    (deleted j).image fun x =>
      (j, deletedVectorToFinTuple j x)

end SimplexHypergraph

noncomputable def diagonalCoverColor
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) :=
  Classical.choose
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

@[simp]
theorem diagonalCoverColor_mem
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    deleteCoordinate (diagonalAPSimplex r N A p)
        (diagonalCoverColor r N A deleted hcover p) ∈
      deleted (diagonalCoverColor r N A deleted hcover p) :=
  Classical.choose_spec
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

noncomputable def diagonalCoveredSlot
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) × (Fin (r + 1) → ZMod N) :=
  let j := diagonalCoverColor r N A deleted hcover p
  (j, deletedVectorToFinTuple j
    (deleteCoordinate (diagonalAPSimplex r N A p) j))

@[simp]
theorem card_diagonalAPParameter
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    Fintype.card (DiagonalAPParameter r N A) =
      A.card * N ^ r := by
  simp [DiagonalAPParameter, ZMod.card]

@[simp]
theorem deletionCapacity_zmod
    (r N : ℕ) [NeZero N] :
    SimplexHypergraph.deletionCapacity
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [SimplexHypergraph.deletionCapacity, DeletedVector,
    Fintype.card_pi, ZMod.card]

def HasUniformCyclicPartiteSimplexRemoval (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N],
        ∀ H :
            SimplexHypergraph (fun _ : Fin k => ZMod N),
          H.toWeighted.simplexCount < c →
            ∃ deleted :
                SimplexHypergraph.DeletionFamily
                  (fun _ : Fin k => ZMod N),
              H.IsSimplexCover deleted ∧
                SimplexHypergraph.normalizedDeletionCost
                    deleted ≤ ε

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

@[simp]
theorem deletedVectorToFinTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedVectorToFinTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedVectorToFinTuple]

@[simp]
theorem finTupleToDeletedVector_deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j
        (deletedVectorToFinTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

noncomputable def deletedVectorFinTupleEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedVectorToFinTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedVectorToFinTuple j
  right_inv := deletedVectorToFinTuple_finTupleToDeletedVector j

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    deletedVectorToFinTuple j (deleteCoordinate x j) =
      orderedFaceTuple (orderedFacet j) x := by
  rfl

@[simp]
theorem finTupleToDeletedVector_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    finTupleToDeletedVector j
        (orderedFaceTuple (orderedFacet j) x) =
      deleteCoordinate x j := by
  rw [←
    finTupleToDeletedVector_deletedVectorToFinTuple j
      (deleteCoordinate x j)]
  congr

noncomputable def SimplexHypergraph.toOrderedPattern
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    OrderedPattern G (n + 1) n where
  edge e y :=
    let j := (orderedFacetEquiv n).symm e
    H.edge j (finTupleToDeletedVector j y)

@[simp]
theorem SimplexHypergraph.toOrderedPattern_edge_orderedFacet
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.toOrderedPattern.edge (orderedFacet j) y ↔
      H.edge j (finTupleToDeletedVector j y) := by
  change
    H.edge ((orderedFacetEquiv n).symm (orderedFacet j))
        (finTupleToDeletedVector
          ((orderedFacetEquiv n).symm (orderedFacet j)) y) ↔
      H.edge j (finTupleToDeletedVector j y)
  have hj :
      (orderedFacetEquiv n).symm (orderedFacet j) = j := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).symm_apply_apply j
  rw [hj]

noncomputable def orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (orderedFacet j)).image
      (finTupleToDeletedVector j)

@[simp]
theorem mem_orderedDeletionToSimplex_iff
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ orderedDeletionToSimplex D j ↔
      deletedVectorToFinTuple j x ∈ D (orderedFacet j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨deletedVectorToFinTuple j x, hx,
        finTupleToDeletedVector_deletedVectorToFinTuple j x⟩

@[simp]
theorem card_orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (orderedDeletionToSimplex D j).card =
      (D (orderedFacet j)).card := by
  classical
  rw [orderedDeletionToSimplex,
    Finset.card_image_of_injective _]
  intro y z hyz
  have htuple :=
    congrArg (deletedVectorToFinTuple j) hyz
  simpa using htuple

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedBoundaryPartition
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

@[simp]
theorem orderedFaceTuple_eraseBoundaryFace
    {G : Type*} {k j : ℕ}
    (e : OrderedFace k (j + 1)) (i : Fin (j + 1))
    (x : Fin k → G) :
    orderedFaceTuple (eraseBoundaryFace e i) x =
      eraseBoundaryCoordinate i (orderedFaceTuple e x) :=
  rfl

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.HomogeneousLieSpan
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace LieGradingExpansion

variable {v : I → L} {g : I → σ →₀ ℕ} (E : LieGradingExpansion v g)

theorem component_tree [DecidableEq σ] (α : σ →₀ ℕ) (a : FreeMagma I) :
    E.component α (lieTreeEval v a) =
      if lieTreeMultidegree g a = α then lieTreeEval v a else 0 := by
  classical
  rw [component_apply, E.expand_tree, coefficients_monomial]
  simp only [Finsupp.single_apply]

end LieGradingExpansion
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedLieSpan
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem markedLieSpan_zero_marked (v : I → L) (w : I → ℕ) (marked : I → Bool) (d l : ℕ) :
    markedLieSpan v w marked d 0 l = weightedLieDegreeLengthSpan v w d l := by
  unfold markedLieSpan weightedLieDegreeLengthSpan
  congr 1
  ext x
  simp only [Nat.zero_le, true_and]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CylinderJointMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators

structure FiniteProbabilityCoupling {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y) where
  law : FiniteProbabilityWeights (X × Y)
  left_mean : ∀ f : X → ℝ, law.mean (fun z => f z.1) = p.mean f
  right_mean : ∀ f : Y → ℝ, law.mean (fun z => f z.2) = q.mean f

noncomputable def FiniteProbabilityCoupling.ofKernel {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (K : X → FiniteProbabilityWeights Y)
    (hK : ∀ f : Y → ℝ, p.mean (fun x => (K x).mean f) = q.mean f) :
    FiniteProbabilityCoupling p q where
  law := p.joint K
  left_mean f := by simp only [FiniteProbabilityWeights.joint_mean, FiniteProbabilityWeights.mean_const]
  right_mean f := by rw [FiniteProbabilityWeights.joint_mean]; exact hK f

end Erdos3

end

end OAI
end


