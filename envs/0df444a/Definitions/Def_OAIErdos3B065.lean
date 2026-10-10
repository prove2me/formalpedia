-- Prove2me | Definitions.Def_OAIErdos3B065
-- name    : OAIErdos3B065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T11:16:46.137017+00:00
-- url     : https://prove2.me/theorems/072cb297-5d6e-4bf7-b315-16fe4db5f75f
-- title:
--   OpenAI Erdős-3 split, definitions bundle 66 of 207
-- statement:
--   Definitions bundle 66 of 207 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B064`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 66 available.
--
--   Modules: `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.comparison_free_top_frequency`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.comparison_space_top_frequency`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_covered_comparison`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_covered_factored_family`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.native_comparison_frequency_zero`, `OAI.Erdos3.NativeRankRelation.CommonData.commonAffineMarkedLift_phase`, `OAI.Erdos3.NativeRankRelation.CommonData.commonAffineMarkedLift_shift_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.comparisonCoefficientSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.comparisonCoefficientSpace_le_layer`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coefficientFreeSpan_projector`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_comparisonCoefficientBases`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_comparison_model`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_factored_comparison_orbit`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_common_projection`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_shared_free_filtered_common`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedLift`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedLift_base_projection`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedLift_conjugation`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedLift_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedLift_pure`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedOrbit_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedOrbit_lift_factorization`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedOrbit_right_normalization`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedSmallElement`, `OAI.Erdos3.NativeRankRelation.CommonData.localPhaseMarkedSmallElement_inv`, `OAI.Erdos3.NativeRankRelation.CommonData.markedDependentEvaluation`, `OAI.Erdos3.NativeRankRelation.CommonData.markedDependentEvaluation_real_map`, `OAI.Erdos3.NativeRankRelation.CommonData.realAffineMarkedBase_shift_eval`, `OAI.Erdos3.NativeRankRelation.CommonData.realAffineMarkedSlope_zero`, `OAI.Erdos3.NativeRankRelation.CommonData.scaledLocalAffineCorrectingElement_eq_parameter`, `OAI.Erdos3.NativeRankRelation.CommonData.scaledLocalAffineCorrectingElement_mem_realLattice`, `OAI.Erdos3.SubspaceFreeLift.exists_native_pair_model`, `OAI.Erdos3.SubspaceFreeLift.exists_uniform_lower_pair_model`, `OAI.Erdos3.dependent_le_refined_firstProjection`, `OAI.Erdos3.exists_controlled_subspace_image_section`, `OAI.Erdos3.exists_controlled_subspace_projector`, `OAI.Erdos3.exists_logHeight_subspace_image_section`, `OAI.Erdos3.exists_markedShiftModel_budget`, `OAI.Erdos3.exists_nativeLowerPairModelBudget_bound`, `OAI.Erdos3.four_projection_petal_add_invariant`, `OAI.Erdos3.le_markedShiftInputBudget`, `OAI.Erdos3.markedEvaluationHeight_le_exp`, `OAI.Erdos3.markedEvaluation_extra_height_bound`, `OAI.Erdos3.markedQuotientHeight_le_exp`, `OAI.Erdos3.markedQuotientPhase_real_map`, `OAI.Erdos3.markedQuotient_final_height_bound`, `OAI.Erdos3.markedQuotient_projection_height_bound`, `OAI.Erdos3.markedQuotient_source_height_bound`, `OAI.Erdos3.markedShiftHeightBudget`, `OAI.Erdos3.markedShiftHeightBudget_le_model`, `OAI.Erdos3.markedShiftHeightBudget_nonneg`, `OAI.Erdos3.markedShiftInputBudget`, `OAI.Erdos3.markedShiftInputBudget_le_height`, `OAI.Erdos3.markedShiftInputBudget_nonneg`, `OAI.Erdos3.markedShiftModelBudget`, `OAI.Erdos3.markedShift_dimension_budget`, `OAI.Erdos3.nativeLowerPairModelBudget`, `OAI.Erdos3.nativePairModelConstant`, `OAI.Erdos3.realMarkedAffineShift_phase`, `OAI.Erdos3.realMarkedParameterDirection_coordinate`, `OAI.Erdos3.realMarkedParameterDirection_coordinate_le`, `OAI.Erdos3.realMarkedPolynomialLift_phase`, `OAI.Erdos3.realMarkedShiftTranslate_phase`, `OAI.Erdos3.real_four_projection_grid`, `OAI.Erdos3.real_four_projection_norm_le`, `OAI.Erdos3.realifyCoordinateMap_eq_coordinates`, `OAI.Erdos3.realify_basis_coordinates`, `OAI.Erdos3.refined_firstProjection_le_common`, `OAI.Erdos3.sharedFreeCommonCorrectionBudget`, `OAI.Erdos3.sharedFreeComparisonBasisBudget_nonneg`, `OAI.Erdos3.sharedFreeComparisonModelBudget`, `OAI.Erdos3.sharedFreeLowerComparisonBudget`, `OAI.Erdos3.step_le_markedShiftInputBudget`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B205

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.MarkedEvaluationHeightBudget
namespace OAI

section

namespace Erdos3

theorem markedQuotient_source_height_bound (s n a d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    let T := lieTreeHeight n H s
    let U := max T (s + 1)
    (((a + 1) * (rationalSolveHeight d T * T) ^ a : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((6 * s + 4) * 11)) ∧
      (rationalLieStructureHeight a (max U (rationalSolveHeight d U)) : ℝ) ≤
        Real.exp ((p + 2) ^ ((6 * s + 4) * 11)) := by
  let k := 6 * s + 2
  let K := (p + 2) ^ k
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  have hpK : p ≤ K := le_power_budget hp (by dsimp [k]; omega)
  have hT : (T : ℝ) ≤ Real.exp K := lieTreeHeight_le_exp n H s hp hn hH
  have hU : (U : ℝ) ≤ Real.exp K := by
    change ((max T (s + 1) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    refine max_le hT ?_
    calc
      (s + 1 : ℕ) ≤ p := hs
      _ ≤ p + 1 := by linarith
      _ ≤ Real.exp p := Real.add_one_le_exp p
      _ ≤ Real.exp K := Real.exp_le_exp.mpr hpK
  have hB₀ := embedding_coordinate_height_budget a d T T
    (show 0 ≤ K by dsimp [K]; positivity) (ha.trans hpK) (hd.trans hpK) hT hT
  have hB := exponential_budget_comp hp (show 0 ≤ K by dsimp [K]; positivity) k 8 le_rfl hB₀
  have hC₀ := rationalLieStructureHeight_inverse_budget a d U
    (show 0 ≤ K by dsimp [K]; positivity) (ha.trans hpK) (hd.trans hpK) hU
  have hC := exponential_budget_comp hp (show 0 ≤ K by dsimp [K]; positivity) k 11 le_rfl hC₀
  refine ⟨hB.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) ?_)), ?_⟩
  · dsimp [k]
    omega
  · simpa only [k, show 6 * s + 2 + 2 = 6 * s + 4 by omega] using hC

theorem markedQuotient_projection_height_bound (m B C v : ℕ) (hv : 1 ≤ v)
    {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ v))
    (hC : (C : ℝ) ≤ Real.exp ((p + 2) ^ v)) :
    (rationalKernelHeight m B : ℝ) ≤ Real.exp ((p + 2) ^ ((v + 2) * 7)) ∧
      ((max 1 (max C (rationalKernelHeight m B)) : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ ((v + 2) * 7)) := by
  have hQ₀ := rationalKernelHeight_le_budget m B
    (show 0 ≤ (p + 2) ^ v by positivity) (hm.trans (le_power_budget hp hv)) hB
  have hQ := exponential_budget_comp hp (show 0 ≤ (p + 2) ^ v by positivity) v 7 le_rfl hQ₀
  refine ⟨hQ, ?_⟩
  rw [Nat.cast_max, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) (max_le ?_ hQ)
  exact hC.trans (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by omega : v ≤ (v + 2) * 7)))

theorem markedQuotient_final_height_bound (d q B Q J w : ℕ) (hw : 1 ≤ w)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hJ : (J : ℝ) ≤ Real.exp ((p + 2) ^ w)) :
    ((max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
      ((d + 1) * (B * Q) ^ d) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ ((w + 2) * 11)) := by
  let W := (p + 2) ^ w
  have hpW : p ≤ W := le_power_budget hp hw
  have hCQ₀ := rationalLieStructureHeight_inverse_budget d q J
    (show 0 ≤ W by dsimp [W]; positivity) (hd.trans hpW) (hq.trans hpW) hJ
  have hCQ := exponential_budget_comp hp (show 0 ≤ W by dsimp [W]; positivity) w 11 le_rfl hCQ₀
  have hproduct : ((B * Q : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 1)) := by
    rw [Nat.cast_mul]
    calc
      (B : ℝ) * Q ≤ Real.exp W * Real.exp W :=
        mul_le_mul hB hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (W + W) := (Real.exp_add W W).symm
      _ ≤ Real.exp ((p + 2) ^ (w + 1)) := by
        apply Real.exp_le_exp.mpr
        calc
          W + W = 2 * W := by ring
          _ ≤ (p + 2) * W := mul_le_mul_of_nonneg_right (by linarith) (by dsimp [W]; positivity)
          _ = (p + 2) ^ (w + 1) := by dsimp [W]; rw [pow_succ]; ring
  have hLQ := rational_sum_cost_le_exp d (B * Q) hp (w + 1) 1 hproduct
    (by simpa only [pow_one] using hd.trans (by linarith : p ≤ p + 2))
  rw [Nat.cast_max]
  refine max_le hCQ (hLQ.trans (Real.exp_le_exp.mpr ?_))
  exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by omega : w + 1 + 1 + 1 ≤ (w + 2) * 11)

theorem markedQuotientHeight_le_exp (s n a d m q H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    (markedQuotientHeight s n a d m q H : ℝ) ≤ Real.exp ((p + 2) ^ (5082 * s + 3564)) := by
  let v := (6 * s + 4) * 11
  let w := (v + 2) * 7
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  let J := max 1 (max C Q)
  obtain ⟨hB, hC⟩ := markedQuotient_source_height_bound s n a d H hp hs hn ha hd hH
  obtain ⟨hQ, hJ⟩ := markedQuotient_projection_height_bound m B C v
    (by dsimp [v]; omega) hp hm hB hC
  have hBW : (B : ℝ) ≤ Real.exp ((p + 2) ^ w) := hB.trans (Real.exp_le_exp.mpr
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by dsimp [w]; omega : v ≤ w)))
  have h := markedQuotient_final_height_bound d q B Q J w (by dsimp [w]; omega) hp hd hq hBW hQ hJ
  have he : (w + 2) * 11 = 5082 * s + 3564 := by dsimp [w, v]; omega
  change ((max (rationalLieStructureHeight d (max J (rationalSolveHeight q J)))
    ((d + 1) * (B * Q) ^ d) : ℕ) : ℝ) ≤ _
  simpa only [he] using h

end Erdos3

end

section

namespace Erdos3

noncomputable def markedShiftInputBudget (s : ℕ) (p : ℝ) : ℝ :=
  p * (s + 1 : ℕ) * (p + 1) ^ s + p + (s + 1 : ℕ)

noncomputable def markedShiftHeightBudget (s : ℕ) (p : ℝ) : ℝ :=
  (markedShiftInputBudget s p + 2) ^ (5082 * s + 3564)

noncomputable def markedShiftModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  markedShiftHeightBudget s p +
    (markedShiftHeightBudget s p + (bchIntegralDenominatorBound (s + 1) + 5 : ℕ)) ^
      (bchIntegralDenominatorBound (s + 1) + 5)

theorem markedShiftInputBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  positivity

theorem le_markedShiftInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  exact (le_add_of_nonneg_left (by positivity)).trans
    (le_add_of_nonneg_right (Nat.cast_nonneg _))

theorem step_le_markedShiftInputBudget (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (s + 1 : ℕ) ≤ markedShiftInputBudget s p := by
  unfold markedShiftInputBudget
  exact le_add_of_nonneg_left (by positivity)

theorem markedShift_dimension_budget (s n t : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) :
    ((n * (s + 1) * (t + 1) ^ s + t : ℕ) : ℝ) ≤ markedShiftInputBudget s p := by
  calc
    _ ≤ p * (s + 1 : ℕ) * (p + 1) ^ s + p := by
      push_cast
      gcongr
    _ ≤ _ := le_add_of_nonneg_right (Nat.cast_nonneg (s + 1))

theorem markedShiftInputBudget_le_height (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftInputBudget s p ≤ markedShiftHeightBudget s p :=
  le_power_budget (markedShiftInputBudget_nonneg s hp) (by omega)

theorem markedShiftHeightBudget_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ markedShiftHeightBudget s p :=
  (markedShiftInputBudget_nonneg s hp).trans (markedShiftInputBudget_le_height s hp)

theorem markedShiftHeightBudget_le_model (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    markedShiftHeightBudget s p ≤ markedShiftModelBudget s p :=
  le_add_of_nonneg_right (pow_nonneg
    (add_nonneg (markedShiftHeightBudget_nonneg s hp) (Nat.cast_nonneg _)) _)

theorem exists_markedShiftModel_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → markedShiftModelBudget s p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X * Polynomial.C (s + 1) * (Polynomial.X + 1) ^ s +
    Polynomial.X + Polynomial.C (s + 1)
  let U : Polynomial ℕ := (Q + 2) ^ (5082 * s + 3564)
  let K := bchIntegralDenominatorBound (s + 1) + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [markedShiftModelBudget, markedShiftHeightBudget, markedShiftInputBudget,
    Q, U, K, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom] using h p hp

end Erdos3

end

section

namespace Erdos3

theorem markedEvaluation_extra_height_bound (n d q T Q K w : ℕ) (hw : 1 ≤ w)
    {p : ℝ} (hp : 0 ≤ p) (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hT : (T : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hQ : (Q : ℝ) ≤ Real.exp ((p + 2) ^ w))
    (hK' : (K : ℝ) ≤ Real.exp ((p + 2) ^ w)) :
    (((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ ((w + 3 + 2) * 8)) := by
  let W := (p + 2) ^ w
  have hpW : p ≤ W := le_power_budget hp hw
  have hW : 0 ≤ W := hp.trans hpW
  have hproduct : ((T * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 1)) := by
    rw [Nat.cast_mul]
    calc
      (T : ℝ) * K ≤ Real.exp W * Real.exp W :=
        mul_le_mul hT hK' (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (W + W) := (Real.exp_add W W).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          W + W = 2 * W := by ring
          _ ≤ (p + 2) * W := mul_le_mul_of_nonneg_right (by linarith) hW
          _ = (p + 2) ^ (w + 1) := by dsimp [W]; rw [pow_succ]; ring
  have hinner : (((n + 1) * (T * K) ^ n : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 3)) := by
    simpa only [show w + 1 + 1 + 1 = w + 3 by omega] using
      rational_sum_cost_le_exp n (T * K) hp (w + 1) 1 hproduct
        (by simpa only [pow_one] using hn.trans (by linarith : p ≤ p + 2))
  have hWW : W ≤ (p + 2) ^ (w + 3) :=
    pow_le_pow_right₀ (by linarith) (by omega : w ≤ w + 3)
  have hA : ((max T ((n + 1) * (T * K) ^ n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (w + 3)) := by
    rw [Nat.cast_max]
    exact max_le (hT.trans (Real.exp_le_exp.mpr hWW)) hinner
  have hpV : p ≤ (p + 2) ^ (w + 3) := hpW.trans hWW
  have hV : 0 ≤ (p + 2) ^ (w + 3) := hp.trans hpV
  have heval := embedding_coordinate_height_budget d q Q (max T ((n + 1) * (T * K) ^ n))
    hV (hd.trans hpV) (hq.trans hpV) (hQ.trans (Real.exp_le_exp.mpr hWW)) hA
  exact exponential_budget_comp hp hV (w + 3) 8 le_rfl heval

theorem markedEvaluationHeight_le_exp (s n a d m q H K : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hs : (s + 1 : ℕ) ≤ p) (hn : (n : ℝ) ≤ p) (ha : (a : ℝ) ≤ p)
    (hd : (d : ℝ) ≤ p) (hm : (m : ℝ) ≤ p) (hq : (q : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    (markedEvaluationHeight s n a d m q H K : ℝ) ≤
      Real.exp ((p + 2) ^ (5082 * s + 3564)) := by
  let v := (6 * s + 4) * 11
  let w := (v + 2) * 7
  let T := lieTreeHeight n H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  let Q := rationalKernelHeight m B
  have hw : 1 ≤ w := by dsimp [w, v]; omega
  have hpW : p ≤ (p + 2) ^ w := le_power_budget hp hw
  obtain ⟨hB, hC⟩ := markedQuotient_source_height_bound s n a d H hp hs hn ha hd hH
  obtain ⟨hQ, _⟩ := markedQuotient_projection_height_bound m B C v
    (by dsimp [v]; omega) hp hm hB hC
  have hT : (T : ℝ) ≤ Real.exp ((p + 2) ^ w) :=
    (lieTreeHeight_le_exp n H s hp hn hH).trans (Real.exp_le_exp.mpr
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by dsimp [w, v]; omega : 6 * s + 2 ≤ w)))
  have heval := markedEvaluation_extra_height_bound n d q T Q K w hw hp hn hd hq hT hQ
    (hK.trans (Real.exp_le_exp.mpr hpW))
  change ((max (markedQuotientHeight s n a d m q H)
    ((d + 1) * (rationalSolveHeight q Q * max T ((n + 1) * (T * K) ^ n)) ^ d) : ℕ) : ℝ) ≤ _
  rw [Nat.cast_max]
  refine max_le (markedQuotientHeight_le_exp s n a d m q H hp hs hn ha hd hm hq hH) ?_
  exact heval.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith)
    (by dsimp [w, v]; omega : (w + 3 + 2) * 8 ≤ 5082 * s + 3564)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeCommonProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem dependent_le_refined_firstProjection
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C D : Submodule R V) (K : Submodule R (Fin 4 → V)) :
    D ≤ (fourRefinedRelation C D K).map (LinearMap.proj 0) := by
  intro v hv
  refine ⟨fun _ : Fin 4 => v, fourBalancedDependent_le_refined C D K ?_, rfl⟩
  exact (mem_fourBalancedDependent D _).mpr ⟨fun _ => hv, by abel⟩

theorem real_four_projection_norm_le
    {V ι : Type*} [LieRing V] [LieAlgebra ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) :
    ‖(b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x)‖ ≤
      ‖((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x) i| ≤ _
  rw [real_pi_projection_coordinates]
  exact norm_le_pi_norm (((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x) ⟨k, i⟩

theorem real_four_projection_grid
    {V ι : Type*} [LieRing V] [LieAlgebra ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] (Fin 4 → V)) (k : Fin 4) (l : ℕ)
    (hx : ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun ((LinearMap.proj k).baseChange ℝ x) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => z ⟨k, i⟩, funext fun i => ?_⟩
  exact (congrFun hz ⟨k, i⟩).trans (congrArg (fun a : ℝ => (l : ℝ) * a)
    (real_pi_projection_coordinates b x k i).symm)

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_common_projection
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      ∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d) := by
  intro Λ
  classical
  let z := 8 * sharedRefinementInputBudget s P' + 1
  let A₀ := sharedFreeEquationInputBudget s Q P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hbudget := (sharedFreeAffineConstant_spec s).2 Q P' hQ hQP' hP' 0
    (by simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg s)) hP')
  have hcut := sharedFreeRecoveryThreshold_spec s hQ hP' N
    ((Real.exp_le_exp.mpr hbudget.1).trans hN)
  have hb := sharedFreeEquationInputBudget_bounds s hQ hP'
  have hA₀ : 0 ≤ A₀ := hb.1
  have hcoeff := sharedFreeRecoveryThreshold_coefficient_bounds s hQ hP'
  have hAΛ : A₀ ≤ Λ :=
    (le_power_budget hb.1 (by decide : 1 ≤ 4)).trans (hcoeff.1.trans hbudget.1)
  have hnum : Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) ≤ Real.exp Λ := by
    have hfac : 1 ≤ 2 * Real.exp ((A₀ + 2) ^ 3) := by
      have h := Real.one_le_exp_iff.mpr (show 0 ≤ (A₀ + 2) ^ 3 by positivity)
      linarith
    calc
      _ ≤ 2 * (Real.exp ((A₀ + 2) ^ 3) *
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z))) := by
        have h := mul_le_mul_of_nonneg_right hfac
          (show 0 ≤ Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z) by positivity)
        simpa only [one_mul, mul_assoc] using h
      _ ≤ _ := hcoeff.2.trans (Real.exp_le_exp.mpr hbudget.1)
  obtain ⟨D₁, _hsub, _hspaces, hcorr⟩ :=
    D.exists_controlled_shared_free_refinement E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hcut.1
  obtain ⟨t, ht⟩ := D₁.nonempty
  choose m hm hmb hcorr using hcorr
  have hdenom (d : Fin s) : (m d : ℝ) ≤ Real.exp Λ :=
    (hmb d).trans (Real.exp_le_exp.mpr (hb.2.2.2.trans hAΛ))
  let π := (LinearMap.proj (0 : Fin 4) :
    (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] D.CoefficientFreeLieAlgebra).baseChange ℝ
  have hcommon (d : Fin s) : ∃ γ e q : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
      γ ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
      coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ + e + q ∧
      ‖(E.basis.baseChange ℝ).equivFun e‖ ≤ Real.exp Λ / (N : ℝ) ^ (d.val + 1) ∧
      (E.basis.baseChange ℝ).equivFun q ∈ realDenominatorGrid (m d) := by
    obtain ⟨A, S, hA, hS, hmem⟩ := hcorr d t ht
    let K := fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)
    let u := coefficients (v (rankQuadrupleParameters t 1)).log (Finsupp.single () (d.val + 1))
    let γ := coefficients ξ.log (Finsupp.single () (d.val + 1)) - π A - π S
    have hhead : π ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
        (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t)) =
          coefficients ξ.log (Finsupp.single () (d.val + 1)) + u := by
      dsimp only [π]
      rw [real_four_projection, LinearEquiv.apply_symm_apply]
      rfl
    have hproj : π ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
        (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t) - A - S) ∈
          (K.map (LinearMap.proj 0)).baseChange ℝ := by
      rw [realification_map]
      exact ⟨_, hmem, rfl⟩
    rw [map_sub, map_sub, hhead] at hproj
    have hu : u ∈ (K.map (LinearMap.proj 0)).baseChange ℝ :=
      Submodule.baseChange_mono ℝ (dependent_le_refined_firstProjection _ _ _) (hv _ d)
    refine ⟨γ, π A, π S, ?_, ?_, ?_, ?_⟩
    · have h := ((K.map (LinearMap.proj 0)).baseChange ℝ).sub_mem hproj hu
      convert h using 1
      dsimp [γ]
      abel
    · dsimp [γ]
      abel
    · have hA' : ‖((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun A‖ ≤
          (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) / (N : ℝ) ^ (d.val + 1) := by
        simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using hA
      exact (real_four_projection_norm_le E.basis A 0).trans
        (hA'.trans (div_le_div_of_nonneg_right hnum (by positivity)))
    · exact real_four_projection_grid E.basis S 0 (m d) hS
  choose γ e q hγ heq he hq using hcommon
  exact ⟨m, γ, e, q, fun d => ⟨hm d, hdenom d, hγ d, heq d, he d, hq d⟩⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3

theorem four_projection_petal_add_invariant
    {R I E : Type*} {V : I → Type*} [CommRing R]
    [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] [AddCommGroup E]
    (f : (∀ i, V i) → E) (K : ∀ i, Submodule R (Fin 4 → V i))
    (hK : ∀ z : ∀ i, Fin 4 → V i, (∀ i, z i ∈ K i) → fourFunctionDifference f z = 0)
    (x p : ∀ i, V i) (hx : ∀ i, x i ∈ (K i).map (LinearMap.proj 0))
    (hp : ∀ i, LinearMap.single R (fun _ : Fin 4 => V i) 0 (p i) ∈ K i) :
    f (x + p) = f x := by
  classical
  have hlift (i : I) : ∃ z ∈ K i, z 0 = x i := hx i
  choose z hz hz0 using hlift
  let y (i : I) := z i + LinearMap.single R (fun _ : Fin 4 => V i) 0 (p i)
  have hy (i : I) : y i ∈ K i := (K i).add_mem (hz i) (hp i)
  have hy0 : (fun i => y i 0) = x + p := by
    funext i
    simp only [y, Pi.add_apply, LinearMap.single_apply, Pi.single_eq_same, hz0]
  have hy1 : (fun i => y i 1) = fun i => z i 1 := by
    funext i
    simp [y, LinearMap.single_apply]
  have hy2 : (fun i => y i 2) = fun i => z i 2 := by
    funext i
    simp [y, LinearMap.single_apply]
  have hy3 : (fun i => y i 3) = fun i => z i 3 := by
    funext i
    simp [y, LinearMap.single_apply]
  have h₀ := hK z hz
  have h₁ := hK y hy
  rw [fourFunctionDifference, hy0, hy1, hy2, hy3] at h₁
  rw [fourFunctionDifference, show (fun i => z i 0) = x from funext hz0] at h₀
  simp only [sub_eq_add_neg] at h₀ h₁
  exact add_right_cancel (add_right_cancel (add_right_cancel (h₁.trans h₀.symm)))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix NNReal

theorem realifyCoordinateMap_eq_coordinates
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (φ : V →ₗ[ℚ] (ι → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap φ x = realRationalCoordinateEquiv (φ.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    funext i
    rw [realifyCoordinateMap_tmul, LinearMap.baseChange_tmul, realRationalCoordinateEquiv_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_controlled_subspace_image_section
    {μ ι κ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hφH : ∀ j i, RationalHeightLE (φ (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3 + (p + 2) ^ 36) ∧
      (∀ y, σ y ∈ U.baseChange ℝ) ∧
      (∀ x ∈ U.baseChange ℝ,
        realifyCoordinateMap φ (σ (realifyCoordinateMap φ x)) = realifyCoordinateMap φ x) ∧
      (∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤
        Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18) * ‖y‖) ∧
      ∀ y ∈ realDenominatorGrid l, (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
  classical
  let A : Matrix ι κ ℚ := fun i j => φ (v j) i
  let B : Matrix μ κ ℚ := fun i j => b.repr (v j) i
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH (fun i j => hφH j i)
  let σ := (b.baseChange ℝ).equivFun.symm.toLinearMap.comp
    ((Matrix.mulVecLin (fun i j => (B i j : ℝ))).comp
      (Matrix.mulVecLin (fun i j => (S i j : ℝ))))
  have hσ (y : ι → ℝ) :
      σ y = realGeneratorCombination v ((fun i j => (S i j : ℝ)) *ᵥ y) := by
    apply (b.baseChange ℝ).equivFun.injective
    change (b.baseChange ℝ).equivFun ((b.baseChange ℝ).equivFun.symm
      ((fun i j => (B i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y))) = _
    rw [LinearEquiv.apply_symm_apply, realGeneratorCombination_coordinates]
  have hcoord (y : ι → ℝ) : (b.baseChange ℝ).equivFun (σ y) =
      (fun i j => (B i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y) := by
    rw [hσ, realGeneratorCombination_coordinates]
  have hvU (j : κ) : v j ∈ U := hv ▸ Submodule.subset_span (Set.mem_range_self j)
  have hvφ : Submodule.span ℚ (Set.range (fun j => φ (v j))) = U.map φ := by
    rw [← hv, Submodule.map_span, ← Set.range_comp]
    rfl
  have hHp' : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
    hHp.trans (Real.exp_le_exp.mpr (by simp))
  have hBden : (matrixDenominator B : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    matrixDenominator_le_exp_power B hp 1 hμ hκ
      (fun i j => (Nat.cast_le.mpr (hvH j i).2).trans hHp')
  have hSden := real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp
  have hfac : ((Fintype.card κ : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ 1 (by decide))
    exact mul_le_mul_of_nonneg_left (add_le_add hHp' le_rfl) (by positivity)
  have hBnorm (y : κ → ℝ) :
      ‖(fun i j => (B i j : ℝ)) *ᵥ y‖ ≤ Real.exp ((p + 2) ^ 3) * ‖y‖ :=
    (norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hvH j i).abs_real_le) y).trans
      (mul_le_mul_of_nonneg_right hfac (norm_nonneg y))
  refine ⟨σ, matrixDenominator B * (matrixDenominator S * l),
    Nat.mul_pos (matrixDenominator_pos B) (Nat.mul_pos (matrixDenominator_pos S) hl),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul hBden hSden (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  · intro y
    rw [hσ]
    exact realGeneratorCombination_mem U v hvU _
  · intro x hx
    have himg : realifyCoordinateMap φ x ∈
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
      rw [← realRationalCoordinateSpan_eq_image (U.map φ) (fun j => φ (v j)) hvφ,
        realifyCoordinateMap_eq_coordinates]
      refine ⟨φ.baseChange ℝ x, ?_, rfl⟩
      rw [realification_map]
      exact ⟨x, hx, rfl⟩
    rw [hσ, realifyCoordinateMap_eq_coordinates, realGeneratorCombination_map_coordinates]
    exact real_matrix_image_section_apply A S hS _ himg
  · intro y
    rw [hcoord]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * ‖(fun i j => (S i j : ℝ)) *ᵥ y‖ := hBnorm _
      _ ≤ Real.exp ((p + 2) ^ 3) * (Real.exp ((p + 2) ^ 18) * ‖y‖) :=
        mul_le_mul_of_nonneg_left (real_image_section_norm_bound S H hSH hp hι hκ hHp y)
          (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, ← Real.exp_add]
  · intro y hy
    rw [hcoord]
    exact real_matrix_denominator_grid B _ _ (real_matrix_denominator_grid S l y hy)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem realify_basis_coordinates
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι]
    (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) :
    realifyCoordinateMap b.equivFun.toLinearMap x = (b.baseChange ℝ).equivFun x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    funext i
    rw [realifyCoordinateMap_tmul]
    change a * (b.repr v i : ℝ) = (b.baseChange ℝ).repr (a ⊗ₜ[ℚ] v) i
    rw [Basis.baseChange_repr_tmul]
    simp only [Rat.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_controlled_subspace_projector
    {μ κ V : Type*} [Fintype μ] [Fintype κ] [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (l : ℕ) (hl : 0 < l)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ j i, rationalLogHeight (b.repr (v j) i) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := p + 1
    ∃ (P : (ℝ ⊗[ℚ] V) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 3 + (q + 2) ^ 36) ∧
      (∀ x, P x ∈ U.baseChange ℝ) ∧ (∀ x ∈ U.baseChange ℝ, P x = x) ∧
      (∀ x, ‖(b.baseChange ℝ).equivFun (P x)‖ ≤
        Real.exp ((q + 2) ^ 3 + (q + 2) ^ 18) * ‖(b.baseChange ℝ).equivFun x‖) ∧
      ∀ x, (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
        (b.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
  intro q
  have hpq : p ≤ q := by dsimp [q]; linarith
  obtain ⟨σ, m, hm, hmp, hσU, hσfix, hσnorm, hσgrid⟩ :=
    exists_controlled_subspace_image_section b U v hv b.equivFun.toLinearMap
      (one_le_ceil_exp p) hl (fun j i => rationalHeightLE_ceil_exp (hvH j i))
      (fun j i => rationalHeightLE_ceil_exp (hvH j i))
      (hp.trans hpq) (hμ.trans hpq) (hμ.trans hpq) (hκ.trans hpq)
      (ceil_exp_le_exp_add_one hp) (hlp.trans (Real.exp_le_exp.mpr hpq))
  let P := σ.comp (b.baseChange ℝ).equivFun.toLinearMap
  refine ⟨P, m, hm, hmp, (fun x => hσU _), ?_, (fun x => hσnorm _), ?_⟩
  · intro x hx
    apply (b.baseChange ℝ).equivFun.injective
    change (b.baseChange ℝ).equivFun (σ ((b.baseChange ℝ).equivFun x)) = _
    simpa only [realify_basis_coordinates] using hσfix x hx
  · intro x hx
    exact hσgrid _ hx

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_logHeight_subspace_image_section
    {μ ι κ V : Type*} [Fintype μ] [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℚ V]
    (b : Basis μ ℚ V) (U : Submodule ℚ V) (v : κ → V)
    (hv : Submodule.span ℚ (Set.range v) = U) (φ : V →ₗ[ℚ] (ι → ℚ))
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hμ : (Fintype.card μ : ℝ) ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hvH : ∀ j i, rationalLogHeight (b.repr (v j) i) ≤ p)
    (hφH : ∀ i j, rationalLogHeight (φ (b i) j) ≤ p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    let t := (p + 2) ^ 4 + 1
    ∃ (σ : (ι → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] V)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
      (∀ y, σ y ∈ U.baseChange ℝ) ∧
      (∀ x ∈ U.baseChange ℝ,
        realifyCoordinateMap φ (σ (realifyCoordinateMap φ x)) = realifyCoordinateMap φ x) ∧
      (∀ y, ‖(b.baseChange ℝ).equivFun (σ y)‖ ≤
        Real.exp ((t + 2) ^ 3 + (t + 2) ^ 18) * ‖y‖) ∧
      ∀ y ∈ realDenominatorGrid l, (b.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
  intro t
  have hp4 : p ≤ (p + 2) ^ 4 := le_power_budget hp (by decide)
  have hpt : p ≤ t := hp4.trans (le_add_of_nonneg_right (by norm_num))
  have ht : 0 ≤ t := hp.trans hpt
  apply exists_controlled_subspace_image_section b U v hv φ
    (one_le_ceil_exp ((p + 2) ^ 4)) hl _ _ ht (hμ.trans hpt) (hι.trans hpt) (hκ.trans hpt)
    (ceil_exp_le_exp_add_one (by positivity)) (hlp.trans (Real.exp_le_exp.mpr hpt))
  · intro j i
    exact rationalHeightLE_ceil_exp ((hvH j i).trans hp4)
  · intro j i
    apply rationalHeightLE_ceil_exp
    exact linearMap_coordinate_logHeight b (Pi.basisFun ℚ ι) φ hp hμ hφH (v j) (hvH j) i

end Erdos3

end

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_native_pair_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L I : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))]
      (r d : ℕ) (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ (Fin 2 → L))
      (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
      (p : ℝ), 2 ≤ p → T.ComplexityLE p →
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => D.basis)).repr
        (B j a : Fin 2 → L) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (T.realSubgroup s r) I p,
      let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
      ∃ E : RationalFilteredNilmanifold (Algebra S r) s (finrank ℚ (Algebra S r)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = filtration S T.filtration.rank_le_degree ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => D)).basis.repr
            (φ (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ (pi (fun _ : Fin 2 => D)).lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) (I × I) ((p + C) ^ C),
             V.frequency = (pairDifferenceFunctional U.frequency).comp φ.toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_model s
  let K₀ : Polynomial ℕ := (Polynomial.X + 2) ^ 2 +
    (Polynomial.X + (Polynomial.X ^ 2 + Polynomial.X + 3) ^ 2 + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ _ _ _ _ r d D T S B hS p hp hT hB U φ
  have hp₀ : 0 ≤ p := by linarith
  let P := p + (p ^ 2 + p + 3) ^ 2 + 2
  let K := (p + 2) ^ 2 + P
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpP : p ≤ P := by dsimp only [P]; nlinarith [sq_nonneg (p ^ 2 + p + 3)]
  have hPK : P ≤ K := le_add_of_nonneg_left (sq_nonneg (p + 2))
  have hGK : (p + 2) ^ 2 ≤ K := le_add_of_nonneg_right hP
  have hK : 0 ≤ K := hP.trans hPK
  have hbound : (K + a) ^ a ≤ (p + C) ^ C := by
    simpa [K₀, K, P, Polynomial.eval₂_pow] using hbudget p hp₀
  let D₂ := pi (fun _ : Fin 2 => D)
  let T₂ := piRank (fun _ : Fin 2 => D) (fun _ => T)
  have hT₂ : T₂.ComplexityLE K :=
    (piRank_complexity (fun _ : Fin 2 => D) (fun _ => T) hp₀
      (by simpa using hp) (fun _ => hT)).mono T₂ hGK
  have hB₂ (j : Fin s) (k : Fin (finrank ℚ (S j))) (i) :
      rationalLogHeight (D₂.basis.repr (B j k : Fin 2 → L) i) ≤ K := by
    change rationalLogHeight ((productFinBasis (fun _ : Fin 2 => D)).repr _ i) ≤ K
    rw [productFinBasis, Basis.repr_reindex_apply]
    exact (hB j k _).trans (hpP.trans hPK)
  obtain ⟨E, Q, hQ, hQc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree (Fin 2 → L) (I × I) r _ D₂ T₂ S B hS K hK hT₂ hB₂
      ((U.paired T hp hT.1).mono hPK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  exact ⟨E, Q, hQ, hQc.mono Q hbound, hcentral, ⟨frame.mono hbound⟩,
    (fun i j => (hmatrix i j).trans hbound), hlattice, V.mono hbound, hfreq, hobs⟩

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_coefficientFreeSpan_projector (hs : 1 ≤ s) (d : Fin s)
    (l : ℕ) (hl : 0 < l) {A : ℝ} (hA : 0 ≤ A) (hQA : Q ≤ A)
    (hdim : (finrank ℚ D.CoefficientFreeLieAlgebra : ℝ) ≤ A)
    (hlA : (l : ℝ) ≤ Real.exp A) :
    let t := A + 1
    ∃ (P : (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) →ₗ[ℝ]
        (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
      (∀ x, P x ∈ (D.coefficientFreeSpan d).baseChange ℝ) ∧
      (∀ x ∈ (D.coefficientFreeSpan d).baseChange ℝ, P x = x) ∧
      (∀ x, ‖(e.baseChange ℝ).equivFun (P x)‖ ≤
        Real.exp ((t + 2) ^ 3 + (t + 2) ^ 18) * ‖(e.baseChange ℝ).equivFun x‖) ∧
      ∀ x, (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
        (e.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis e F hs d
  have hcspan : Submodule.span ℚ (Set.range (fun j => (c j : D.CoefficientFreeLieAlgebra))) =
      D.coefficientFreeSpan d := by
    change Submodule.span ℚ (Set.range ((D.coefficientFreeSpan d).subtype ∘ c)) = _
    rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  apply exists_controlled_subspace_projector e (D.coefficientFreeSpan d)
    (fun j => (c j : D.CoefficientFreeLieAlgebra)) hcspan l hl hA
  · simpa only [Fintype.card_fin] using hdim
  · have hd : (finrank ℚ (D.coefficientFreeSpan d) : ℝ) ≤
        finrank ℚ D.CoefficientFreeLieAlgebra := by
      exact_mod_cast Submodule.finrank_le (D.coefficientFreeSpan d)
    simpa only [Fintype.card_fin] using hd.trans hdim
  · exact fun j i => (hc j i).trans hQA
  · exact hlA

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreeCommonCorrectionBudget (s : ℕ) (q p : ℝ) : ℝ :=
  let Λ := (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let t := (q + p + Λ) + 1
  (t + 2) ^ 3 + (t + 2) ^ 36 + Λ

theorem refined_firstProjection_le_common
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (C D : Submodule R V) (hDC : D ≤ C) (K : Submodule R (Fin 4 → V)) :
    (fourRefinedRelation C D K).map (LinearMap.proj 0) ≤ C := by
  rintro v ⟨w, hw, rfl⟩
  exact ((mem_fourCommonModulo C D w).mp (fourRefinedRelation_le_common C D hDC K hw)).1 0

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_filtered_common
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let L := sharedFreeCommonCorrectionBudget s Q P'
    ∃ (m : Fin s → ℕ) (γ e q : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
      ∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp L ∧
        γ d ∈ ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ ∧
        γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        e d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        q d ∈ (D.coefficientFreeSpan d).baseChange ℝ ∧
        coefficients ξ.log (Finsupp.single () (d.val + 1)) = γ d + e d + q d ∧
        ‖(E.basis.baseChange ℝ).equivFun (e d)‖ ≤ Real.exp L / (N : ℝ) ^ (d.val + 1) ∧
        (E.basis.baseChange ℝ).equivFun (q d) ∈ realDenominatorGrid (m d) := by
  intro L
  classical
  obtain ⟨l, γ, e, q, hdata⟩ :=
    D.exists_shared_free_common_projection E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let A := Q + P' + Λ
  let t := A + 1
  let C := (t + 2) ^ 3 + (t + 2) ^ 18
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hP' (Nat.cast_nonneg _)) _
  have hA : 0 ≤ A := add_nonneg (add_nonneg hQ hP') hΛ
  have hQA : Q ≤ A := (le_add_of_nonneg_right hP').trans (le_add_of_nonneg_right hΛ)
  have hPA : P' ≤ A := (le_add_of_nonneg_left hQ).trans (le_add_of_nonneg_right hΛ)
  have hΛA : Λ ≤ A := le_add_of_nonneg_left (add_nonneg hQ hP')
  have hprojectors (d : Fin s) :
      ∃ (P : (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) →ₗ[ℝ]
          (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
        (∀ x, P x ∈ (D.coefficientFreeSpan d).baseChange ℝ) ∧
        (∀ x ∈ (D.coefficientFreeSpan d).baseChange ℝ, P x = x) ∧
        (∀ x, ‖(E.basis.baseChange ℝ).equivFun (P x)‖ ≤
          Real.exp C * ‖(E.basis.baseChange ℝ).equivFun x‖) ∧
        ∀ x, (E.basis.baseChange ℝ).equivFun x ∈ realDenominatorGrid (l d) →
          (E.basis.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
    exact D.exists_coefficientFreeSpan_projector E.basis F (by omega) d
      (l d) (hdata d).1 hA hQA ((hT.1.1.trans hQP').trans hPA)
      ((hdata d).2.1.trans (Real.exp_le_exp.mpr hΛA))
  choose P m hm hmb hPU hPfix hPnorm hPgrid using hprojectors
  have ht : 0 ≤ t := add_nonneg hA zero_le_one
  have h18 : (t + 2) ^ 18 ≤ (t + 2) ^ 36 := pow_le_pow_right₀ (by linarith only [ht]) (by decide)
  have hL : L = (t + 2) ^ 3 + (t + 2) ^ 36 + Λ := rfl
  have hCL : C + Λ ≤ L := add_le_add (add_le_add (le_refl ((t + 2) ^ 3)) h18) (le_refl Λ)
  refine ⟨m, γ, (fun d => P d (e d)), (fun d => P d (q d)), ?_⟩
  intro d
  obtain ⟨_hl, _hlb, hγ, heq, herr, hgrid⟩ := hdata d
  have hγC : γ d ∈ (D.coefficientFreeSpan d).baseChange ℝ :=
    Submodule.baseChange_mono ℝ
      (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan d) _) hγ
  have hξC : coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.coefficientFreeSpan d).baseChange ℝ :=
    Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d)
  have hsum : e d + q d ∈ (D.coefficientFreeSpan d).baseChange ℝ := by
    have hh : e d + q d = coefficients ξ.log (Finsupp.single () (d.val + 1)) - γ d := by
      rw [heq]
      abel
    rw [hh]
    exact ((D.coefficientFreeSpan d).baseChange ℝ).sub_mem hξC hγC
  have hsumfix := hPfix d (e d + q d) hsum
  rw [map_add] at hsumfix
  refine ⟨hm d, (hmb d).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hΛ)),
    hγ, hγC, hPU d _, hPU d _, ?_, ?_, hPgrid d _ hgrid⟩
  · calc
      _ = γ d + (e d + q d) := by rw [heq, add_assoc]
      _ = γ d + (P d (e d) + P d (q d)) := by rw [hsumfix]
      _ = _ := (add_assoc _ _ _).symm
  · calc
      _ ≤ Real.exp C * ‖(E.basis.baseChange ℝ).equivFun (e d)‖ := hPnorm d _
      _ ≤ Real.exp C * (Real.exp Λ / (N : ℝ) ^ (d.val + 1)) :=
        mul_le_mul_of_nonneg_left herr (Real.exp_pos _).le
      _ = Real.exp (C + Λ) / (N : ℝ) ^ (d.val + 1) := by rw [← mul_div_assoc, ← Real.exp_add]
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCL) (pow_nonneg (Nat.cast_nonneg N) _)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_space_top_frequency
    (hfreq : V.frequency = B.freeFrequency D) (n : ℕ) (d : Fin n → Fin s)
    (a : FreeMagma (Fin n)) (hd : lieTreeWeight (fun i => (d i).val + 1) a = s)
    (hr : a.length = r) (z : Fin n → Fin 2 → D.CoefficientFreeLieAlgebra)
    (hz : ∀ i, z i ∈ petalComparisonSpace
      ((fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
        (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)).map (LinearMap.proj 0))
      (fourPetalSpace (D.dependentFreeSpan (d i))
        (fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
          (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩)))
      (D.coefficientFreeFiltration.layer ((d i).val + 1) 2)) :
    pairDifferenceFunctional (B.freeFrequency D) (lieTreeEval z a) = 0 := by
  have hC (j : Fin s) :
      (fourRefinedRelation (D.coefficientFreeSpan j) (D.dependentFreeSpan j)
        (D'.coefficientFourSpace ⟨j.val + 1, by omega⟩)).map (LinearMap.proj 0) ≤
          D.coefficientFreeFiltration.layer (j.val + 1) 1 :=
    (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan j) _).trans
      (D.coefficientFreeSpan_le_layer j)
  apply petalComparisonSpace_top_tree D.coefficientFreeFiltration (fun i => (d i).val + 1)
    _ _ (fun i => hC (d i))
    (fun i => (fourPetalSpace_le_first _ _).trans (hC (d i))) (B.freeFrequency D) a hd hr _ z hz
  intro c p hc hp
  apply four_projection_petal_add_invariant
    (fun x => B.freeFrequency D (lieTreeEval x a))
    (fun i => fourRefinedRelation (D.coefficientFreeSpan (d i)) (D.dependentFreeSpan (d i))
      (D'.coefficientFourSpace ⟨(d i).val + 1, by omega⟩))
    (B.correlation_refined_four_identity D E T hbQ hT V g hg D' hfreq n d a hd hr) c p hc
  exact fun i => ((mem_fourPetalSpace _ _ _).mp (hp i)).2

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

noncomputable def comparisonCoefficientSpace (d : Fin s) :
    Submodule ℚ (Fin 2 → D.CoefficientFreeLieAlgebra) :=
  petalComparisonSpace
    ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0))
    (fourPetalSpace (D.dependentFreeSpan d)
      (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))
    (D.coefficientFreeFiltration.layer (d.val + 1) 2)

theorem comparisonCoefficientSpace_le_layer
    (hTfil : T.filtration = D.coefficientFreeFiltration) (d : Fin s) :
    D.comparisonCoefficientSpace E T hbQ hT V g hg D' d ≤
      (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration.layer
        (d.val + 1) 0 := by
  have hC : (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0) ≤
      D.coefficientFreeFiltration.layer (d.val + 1) 1 :=
    (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan d) _).trans
      (D.coefficientFreeSpan_le_layer d)
  change petalComparisonSpace _ _ _ ≤
    Submodule.pi Set.univ (fun _ : Fin 2 => T.filtration.layer (d.val + 1) 0)
  rw [hTfil, D.coefficientFreeFiltration.rank_zero_eq_one]
  exact petalComparisonSpace_le_pi _ _ _ _ hC
    ((fourPetalSpace_le_first _ _).trans hC)
    (D.coefficientFreeFiltration.lex_antitone (Or.inr ⟨rfl, by omega⟩))

include F in
theorem exists_comparisonCoefficientBases
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    ∃ B : ∀ d : Fin s, Basis (Fin (finrank ℚ
        (D.comparisonCoefficientSpace E T hbQ hT V g hg D' d))) ℚ
        (D.comparisonCoefficientSpace E T hbQ hT V g hg D' d),
      ∀ d a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B d a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P' := by
  classical
  choose B hB using fun d => D.exists_sharedFreeComparisonSpace_basis E T hbQ hT F V g hg D'
    hTfil hs hP' hQP' d
  exact ⟨B, hB⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def nativePairModelConstant (s : ℕ) : ℕ :=
  (SubspaceFreeLift.exists_native_pair_model.{0, 0} s).choose

noncomputable def sharedFreeComparisonModelBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (q + 2 + sharedFreeComparisonBasisBudget q p + nativePairModelConstant s) ^ nativePairModelConstant s

theorem sharedFreeComparisonBasisBudget_nonneg {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) :
    0 ≤ sharedFreeComparisonBasisBudget q p := by
  have hA := add_nonneg hq (fourRefinementBasisBudget_nonneg
    (add_nonneg hq (coefficientFourHeightBudget_nonneg hp)))
  exact add_nonneg hA (preimageBasisBudget_nonneg (mul_nonneg (by norm_num) hA))

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_native_comparison_model
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P') :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∃ B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (B j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S B (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
          (finrank ℚ (SubspaceFreeLift.Algebra S r)),
        ∃ U : M.DegreeRankStructure r,
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE (sharedFreeComparisonModelBudget s Q P') ∧ IsCentralLieBasis M.basis ∧
          Nonempty (FreeCoordinateFrame M.basis (sharedFreeComparisonModelBudget s Q P')) ∧
          (∀ i j, rationalLogHeight ((pi (fun _ : Fin 2 => E)).basis.repr
            (φ (M.basis j)) i) ≤ sharedFreeComparisonModelBudget s Q P') ∧
          M.lattice ≤ (pi (fun _ : Fin 2 => E)).lattice.comap (mapOfSteps
            (hL := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s r)
               (Fin W.family.outputDim × Fin W.family.outputDim) (sharedFreeComparisonModelBudget s Q P'),
             Z.frequency = (pairDifferenceFunctional V.frequency).comp φ.toLinearMap ∧
             ∀ i x, Z.observable i (QuotientGroup.mk x) =
               V.pairedObservable T i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ x))) := by
  intro S hS
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hH := sharedFreeComparisonBasisBudget_nonneg hQ hP'
  let K := Q + 2 + sharedFreeComparisonBasisBudget Q P'
  have h2 : 2 ≤ K := by dsimp only [K]; linarith
  have hQK : Q ≤ K := by dsimp only [K]; linarith
  have hHK : sharedFreeComparisonBasisBudget Q P' ≤ K := by dsimp only [K]; linarith
  obtain ⟨B, hB⟩ := D.exists_comparisonCoefficientBases E T hbQ hT F V g hg D' hTfil hs hP' hQP'
  refine ⟨B, hB, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fin 2 → D.CoefficientFreeLieAlgebra))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → D.CoefficientFreeLieAlgebra)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (Pi.basis (fun _ : Fin 2 => E.basis))
  exact (SubspaceFreeLift.exists_native_pair_model s).choose_spec.2
    D.CoefficientFreeLieAlgebra (Fin W.family.outputDim) r _ E T S B hS K h2
    (hT.mono T hQK) (fun j a i => (hB j a i).trans hHK) (V.mono hQK)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem exists_native_factored_comparison_orbit
    (hTfil : T.filtration = D.coefficientFreeFiltration) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1)
    (hK0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 K = 1)
    (hU0 : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1)
    (hA : ∀ d : Fin s, coefficients A.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    let a : Fin 2 → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1) := ![A * K * U, A]
    ∀ (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
        (finrank ℚ (SubspaceFreeLift.Algebra S r))) (Q' : M.DegreeRankStructure r),
      Q'.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      let φ := SubspaceFreeLift.evaluation S B
        (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS
      ∃ u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
        (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
          (SubspaceFreeLift.generatorSpan S r j).baseChange ℝ) ∧
        ∀ i x, RationalFilteredNilmanifold.productProjectionHom (fun _ : Fin 2 => E) i
          (NilpotentLieBCHGroup.realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
            (hM := (RationalFilteredNilmanifold.pi (fun _ : Fin 2 => E)).filtration.lowerCentralSeries_eq_bot) φ
            (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
          E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i) := by
  intro S hS a B M Q' hQ' φ
  apply SubspaceFreeLift.exists_native_pair_orbit E T S B hS M Q' hQ' a
  · intro i
    fin_cases i
    · change E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A * K * U) = 1
      rw [map_mul, map_mul, hA0, hK0, hU0, mul_one, mul_one]
    · exact hA0
  · intro j
    have h := D.paired_affine_orbit_coefficient_mem_comparison E T hbQ hT V g hg D'
      hTfil hs A K U hA hK hU j
    have heq : (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) =
        ![coefficients (A * K * U).log (Finsupp.single () (j.val + 1)),
          coefficients A.log (Finsupp.single () (j.val + 1))] := by
      funext i
      fin_cases i <;> rfl
    rw [heq]
    exact h

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SharedFreeComparisonKernel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CoefficientBases.comparison_free_top_frequency
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (x : SubspaceFreeLift.Algebra S r),
      x ∈ (SubspaceFreeLift.filtration S T.filtration.rank_le_degree).layer s r →
      pairDifferenceFunctional V.frequency
        (SubspaceFreeLift.evaluation S J
          (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS x) = 0 := by
  intro S hS J x hx
  apply FreeDegreeRankLieAlgebra.lift_top_frequency_zero
    (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration
    (SubspaceFreeLift.weight S) (SubspaceFreeLift.weight_pos S)
    (fun a => (J a.1 a.2).val) (fun a => hS a.1 (J a.1 a.2).property)
    (pairDifferenceFunctional V.frequency) _ hx
  intro a hd hr
  classical
  let e := Fintype.equivFin (SubspaceFreeLift.Alphabet S)
  let d : Fin (Fintype.card (SubspaceFreeLift.Alphabet S)) → Fin s := fun i => (e.symm i).1
  let z : Fin (Fintype.card (SubspaceFreeLift.Alphabet S)) → Fin 2 → D.CoefficientFreeLieAlgebra :=
    fun i => (J (e.symm i).1 (e.symm i).2).val
  have hd' : lieTreeWeight (fun i => (d i).val + 1) (FreeMagma.map e a) = s := by
    have heq : (fun i => (d i).val + 1) ∘ e = SubspaceFreeLift.weight S := by
      funext i
      change (e.symm (e i)).1.val + 1 = i.1.val + 1
      rw [e.symm_apply_apply]
    rw [lieTreeWeight_relabel, heq]
    exact hd
  have hr' : (FreeMagma.map e a).length = r := (lieTreeLength_relabel e a).trans hr
  have hz : ∀ i, z i ∈ S (d i) := fun i => (J (e.symm i).1 (e.symm i).2).property
  have h := B.comparison_space_top_frequency D E T hbQ hT V g hg D' hfreq
    (Fintype.card (SubspaceFreeLift.Alphabet S)) d (FreeMagma.map e a) hd' hr' z hz
  have heq : z ∘ e = (fun a : SubspaceFreeLift.Alphabet S => (J a.1 a.2).val) := by
    funext i
    change (J (e.symm (e i)).1 (e.symm (e i)).2).val = (J i.1 i.2).val
    rw [e.symm_apply_apply]
  rw [lieTreeEval_relabel, heq] at h
  rw [hfreq]
  exact h

theorem CoefficientBases.native_comparison_frequency_zero
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B.freeFrequency D) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    ∀ (J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S r) s
        (finrank ℚ (SubspaceFreeLift.Algebra S r))) (U : M.DegreeRankStructure r),
      U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree →
      ∀ η : SubspaceFreeLift.Algebra S r →ₗ[ℚ] ℚ,
        η = (pairDifferenceFunctional V.frequency).comp
          (SubspaceFreeLift.evaluation S J
            (RationalFilteredNilmanifold.piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS).toLinearMap →
        ∀ x ∈ U.filtration.layer s r, η x = 0 := by
  intro S hS J M U hU η hη x hx
  rw [hη]
  change pairDifferenceFunctional V.frequency (SubspaceFreeLift.evaluation S J _ hS x) = 0
  apply B.comparison_free_top_frequency D E T hbQ hT V g hg D' hTfil hfreq J x
  simpa only [hU] using hx

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeLowerComparisonBudget
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeLowerComparisonBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (sharedFreeComparisonModelBudget s q p + rankUnitDescentConstant s) ^ rankUnitDescentConstant s

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison
namespace OAI

section

namespace Erdos3

noncomputable def nativeLowerPairModelBudget (s : ℕ) (p : ℝ) : ℝ :=
  ((p + nativePairModelConstant s) ^ nativePairModelConstant s + rankUnitDescentConstant s) ^
    rankUnitDescentConstant s

theorem exists_nativeLowerPairModelBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
      nativeLowerPairModelBudget s p ≤ (p + C) ^ C := by
  let a := nativePairModelConstant s
  let b := rankUnitDescentConstant s
  let A : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (A + (A + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C := by
    simpa [A, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨(le_add_of_nonneg_right hb).trans hsum, (le_add_of_nonneg_left ha).trans hsum⟩

end Erdos3

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_uniform_lower_pair_model {L I : Type} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure (r + 1))
    (S : Fin s → Submodule ℚ (Fin 2 → L))
    (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
    (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
    {p : ℝ} (hp : 2 ≤ p) (hT : T.ComplexityLE p)
    (hB : ∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => D.basis)).repr
      (B j a : Fin 2 → L) i) ≤ p)
    (V : D.UnitVerticalObservable (T.realSubgroup s (r + 1)) I p)
    (hzero : ∀ x ∈ (filtration S T.filtration.rank_le_degree).layer s (r + 1),
      pairDifferenceFunctional V.frequency
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS x) = 0) :
    let pM := (p + nativePairModelConstant s) ^ nativePairModelConstant s
    let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
    ∃ M : RationalFilteredNilmanifold (Algebra S (r + 1)) s (finrank ℚ (Algebra S (r + 1))),
      ∃ U : M.DegreeRankStructure (r + 1),
        U.filtration = filtration S T.filtration.rank_le_degree ∧ U.ComplexityLE pM ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S (r + 1))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S (r + 1)) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 M.basis
         ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1)) (I × I) pM,
           (∀ i x, Z.observable i (QuotientGroup.mk x) =
             V.pairedObservable T i (QuotientGroup.mk (realificationMap
               (hnil := M.filtration.lowerCentralSeries_eq_bot)
               (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
           M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
             (nativeLowerPairModelBudget s p)) := by
  intro pM φ
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fin 2 → L))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (Pi.basis (fun _ : Fin 2 => D.basis))
  obtain ⟨M, U, hU, hUc, _, _, _, _, hZ⟩ :=
    (exists_native_pair_model.{0, 0} s).choose_spec.2 L I (r + 1) d D T S B hS p hp hT hB V
  refine ⟨M, U, hU, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hfreq, hobs⟩ := hZ
  refine ⟨Z, hobs, ?_⟩
  have hZzero : ∀ x ∈ U.filtration.layer s (r + 1), Z.frequency x = 0 := by
    intro x hx
    rw [hfreq]
    exact hzero x (by simpa only [hU] using hx)
  exact UnitVerticalObservable.hasUniformLowerRankUnitFamily M U Z (fun _ : Unit => 1)
    ((Nat.cast_nonneg _).trans hUc.1.1) hUc hZzero

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_covered_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (Λ : Subgroup E.filtration.Group) (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
    (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m)
    {p₁ : ℝ} (hp₁ : 0 ≤ p₁) (hT₁ : (T.withLattice Λ m hm hin hout).ComplexityLE p₁)
    (V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁)
    (hV₁ : V₁.frequency = V.frequency) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let hS := D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    let E₁ := E.withLattice Λ m hm hin hout
    let T₁ := T.withLattice Λ m hm hin hout
    let pM := (q₁ + nativePairModelConstant s) ^ nativePairModelConstant s
    ∃ J : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j),
      (∀ j a i, rationalLogHeight ((Pi.basis (fun _ : Fin 2 => E.basis)).repr
        (J j a : Fin 2 → D.CoefficientFreeLieAlgebra) i) ≤ sharedFreeComparisonBasisBudget Q P') ∧
      let φ := SubspaceFreeLift.evaluation S J (piRank (fun _ : Fin 2 => E₁) (fun _ => T₁)).filtration hS
      ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
          (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
        ∃ U : M.DegreeRankStructure (r + 1),
          U.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
          U.ComplexityLE pM ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 M.basis
           ∃ Z : M.UnitVerticalObservable (U.realSubgroup s (r + 1))
               (Fin W.family.outputDim × Fin W.family.outputDim) pM,
             (∀ i x, Z.observable i (QuotientGroup.mk x) =
               V₁.pairedObservable T₁ i (QuotientGroup.mk (realificationMap
                 (hnil := M.filtration.lowerCentralSeries_eq_bot)
                 (hM := (pi (fun _ : Fin 2 => E₁)).filtration.lowerCentralSeries_eq_bot) φ x))) ∧
             M.HasUniformLowerRankUnitFamily U Z.observable (fun _ : Unit => 1)
               (nativeLowerPairModelBudget s q₁)) := by
  intro S hS q₁ E₁ T₁ pM
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hB := sharedFreeComparisonBasisBudget_nonneg hQ hP'
  have hq : 2 ≤ q₁ := by dsimp only [q₁]; linarith
  have hpq : p₁ ≤ q₁ := by dsimp only [q₁]; linarith
  have hBq : sharedFreeComparisonBasisBudget Q P' ≤ q₁ := by dsimp only [q₁]; linarith
  obtain ⟨J, hJ⟩ := D.exists_comparisonCoefficientBases E T hbQ hT F V g hg D'
    hTfil hs hP' hQP'
  refine ⟨J, hJ, ?_⟩
  apply SubspaceFreeLift.exists_uniform_lower_pair_model E₁ T₁ S J hS hq
    (hT₁.mono T₁ hpq) (fun j a i => (hJ j a i).trans hBq) (V₁.mono hpq)
  intro x hx
  change pairDifferenceFunctional V₁.frequency
    (SubspaceFreeLift.evaluation S J (piRank (fun _ : Fin 2 => E) (fun _ => T)).filtration hS x) = 0
  rw [hV₁]
  exact B₀.comparison_free_top_frequency D E T hbQ hT V g hg D' hTfil hfreq J x hx

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem CoefficientBases.exists_covered_factored_family {τ : Type*}
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P') (hQP' : Q ≤ P')
    (Λ : Subgroup E.filtration.Group) (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates E.basis Λ)
    (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid m)
    {p₁ : ℝ} (hp₁ : 0 ≤ p₁) (hT₁ : (T.withLattice Λ m hm hin hout).ComplexityLE p₁)
    (V₁ : (E.withLattice Λ m hm hin hout).UnitVerticalObservable
      ((T.withLattice Λ m hm hin hout).realSubgroup s (r + 1)) (Fin W.family.outputDim) p₁)
    (hV₁ : V₁.frequency = V.frequency)
    (A K U : τ → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (A t) = 1)
    (hK0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (K t) = 1)
    (hU0 : ∀ t, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (U t) = 1)
    (hA : ∀ t (d : Fin s), coefficients (A t).log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ t (d : Fin s), coefficients (K t).log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ t (d : Fin s), coefficients (U t).log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ) :
    let S := D.comparisonCoefficientSpace E T hbQ hT V g hg D'
    let q₁ := p₁ + sharedFreeComparisonBasisBudget Q P' + 2
    ∃ M : RationalFilteredNilmanifold (SubspaceFreeLift.Algebra S (r + 1)) s
        (finrank ℚ (SubspaceFreeLift.Algebra S (r + 1))),
      ∃ Tm : M.DegreeRankStructure (r + 1),
        Tm.filtration = SubspaceFreeLift.filtration S T.filtration.rank_le_degree ∧
        Tm.ComplexityLE ((q₁ + nativePairModelConstant s) ^ nativePairModelConstant s) ∧
        M.HasLowerRankOrbitFamily Tm (fun _ : Unit => 1)
          (fun t (i : Fin W.family.outputDim × Fin W.family.outputDim) x =>
            V₁.observable i.1 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t * K t * U t))) *
            star (V₁.observable i.2 (QuotientGroup.mk
              (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (A t)))))
          (nativeLowerPairModelBudget s q₁) := by
  intro S q₁
  let E₁ := E.withLattice Λ m hm hin hout
  let T₁ := T.withLattice Λ m hm hin hout
  obtain ⟨J, _, M, Tm, hTm, hTmc, hZ⟩ :=
    B₀.exists_covered_comparison D E T hbQ hT F V g hg D'
      hTfil hfreq hs hP' hQP' Λ m hm hin hout hp₁ hT₁ V₁ hV₁
  refine ⟨M, Tm, hTm, hTmc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] SubspaceFreeLift.Algebra S (r + 1)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 M.basis
  obtain ⟨Z, hobs, huniform⟩ := hZ
  apply huniform.realizeFamily
  intro t
  obtain ⟨u, hu0, _, hu⟩ := D.exists_native_factored_comparison_orbit E T hbQ hT V g hg D'
    hTfil (by omega) (A t) (K t) (U t) (hA0 t) (hK0 t) (hU0 t) (hA t) (hK t) (hU t)
    J M Tm hTm
  refine ⟨u, hu0, ?_⟩
  intro i x
  exact SubspaceFreeLift.native_pair_observable_eval E₁ T₁ S J
    (D.comparisonCoefficientSpace_le_layer E T hbQ hT V g hg D' hTfil)
    M Tm V₁ Z hobs ![A t * K t * U t, A t] u hu i x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (B₀ : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LocalMarkedLatticeCorrection
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem scaledLocalAffineCorrectingElement_mem_realLattice
    {s r N : ℕ} [NeZero N] {b p q P : ℝ}
    {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
    {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) {d : ℕ}
    (E : RationalFilteredNilmanifold
      (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t) (s + 1) d)
    (hm : ∀ a : Fin t → ℤ,
      (⟨(m : ℚ) • markedQuotientDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice) (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h ∈ E.realLattice := by
  exact markedDirection_mem_realLattice_of_smul D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t E (m : ℚ)
    (fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
    (hm (fun i => -affineCyclicTorusCarry u c h₀ h i))

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalPhaseMarkedObservable
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedOrbit :
    (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
  Mul.mul (α := (D.markedQuotientMultidegree t).realification.PolynomialOrbit)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
    (realMarkedParameterOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t
        (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i) :
      (D.markedQuotientMultidegree t).realification.PolynomialOrbit)

noncomputable def localPhaseMarkedSmallElement (h : ZMod N) :
    (D.markedQuotientMultidegree t).realification.Group :=
  realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)

theorem localPhaseMarkedOrbit_eval (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) =
        (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
          (correlationInput (h.val : ℤ) n)
          (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
        realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t
            (fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)) := by
  let E := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
  let g := D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0
  let a₀ : Fin t → ℝ := fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)
  let a₁ : Fin t → ℝ := fun i => -(m : ℝ) * u i
  let phase : (D.markedQuotientMultidegree t).realification.PolynomialOrbit :=
    realMarkedParameterOrbit D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t a₀ a₁
  have hm : E (D.localPhaseMarkedOrbit t x y u c h₀ m) = E g * E phase := E.map_mul g phase
  apply hm.trans
  apply congrArg (fun z : (D.markedQuotientMultidegree t).realification.Group => E g * z)
  apply (realMarkedParameterOrbit_eval D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t a₀ a₁ (h.val : ℤ) n).trans
  apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
  funext i
  simp only [a₀, a₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  ring

theorem scaledLocalAffineCorrectingElement_eq_parameter (h : ZMod N) :
    D.scaledLocalAffineCorrectingElement t u c h₀ m h =
      realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t
          (fun i => -(m : ℝ) * (affineCyclicTorusCarry u c h₀ h i : ℝ)) := by
  apply NilpotentLieBCHGroup.ext
  have he := realMarkedParameterDirection_rat D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t
      ((m : ℚ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℚ))
  change realMarkedDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t _ =
      realMarkedParameterDirection D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t _
  simpa only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_neg, Rat.cast_natCast,
    Rat.cast_intCast, Int.cast_neg, mul_neg, neg_mul] using he.symm

theorem localPhaseMarkedOrbit_right_normalization (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
        (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹ =
      (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0) *
          D.localPhaseMarkedSmallElement t u c h₀ m h := by
  let par : (Fin t → ℝ) → (D.markedQuotientMultidegree t).realification.Group :=
    realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t
  let a : Fin t → ℝ := fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)
  let b : Fin t → ℝ := fun i => -(m : ℝ) * (affineCyclicTorusCarry u c h₀ h i : ℝ)
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
  have hi : (par b)⁻¹ = par (-b) :=
    realMarkedParameterElement_inv D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t b
  have hab : par a * par (-b) = D.localPhaseMarkedSmallElement t u c h₀ m h := by
    apply (realMarkedParameterElement_mul D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t a (-b)).trans
    apply congrArg par
    funext i
    simp only [a, b, Pi.add_apply, Pi.neg_apply, affineCyclicTorusLocalLift_eq_sub_carry]
    ring
  calc
    _ = (g * par a) * (par b)⁻¹ :=
      congrArg₂ (fun z w : (D.markedQuotientMultidegree t).realification.Group => z * w⁻¹)
        (D.localPhaseMarkedOrbit_eval t x y u c h₀ m h n)
        (D.scaledLocalAffineCorrectingElement_eq_parameter t u c h₀ m h)
    _ = (g * par a) * par (-b) := congrArg (fun z => (g * par a) * z) hi
    _ = g * (par a * par (-b)) := mul_assoc _ _ _
    _ = _ := congrArg (g * ·) hab

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (e : Basis (Fin d) ℚ (MarkedShiftQuotient F v w marked t))

theorem realMarkedParameterDirection_coordinate (a : Fin t → ℝ) (j : Fin d) :
    (e.baseChange ℝ).repr (realMarkedParameterDirection F v w marked t a) j =
      ∑ i, a i * (e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ) := by
  apply (congrArg (fun z => (e.baseChange ℝ).repr z j)
    (realMarkedParameterDirection_apply F v w marked t a)).trans
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    realMarkedDirection, rationalLieInclusion_coordinates]

theorem realMarkedParameterDirection_coordinate_le (a : Fin t → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (ha : ∀ i, |a i| ≤ A)
    (he : ∀ i j, |(e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| ≤ B)
    (j : Fin d) :
    |(e.baseChange ℝ).repr (realMarkedParameterDirection F v w marked t a) j| ≤ (t : ℝ) * A * B := by
  rw [realMarkedParameterDirection_coordinate]
  calc
    _ ≤ ∑ i, |a i * (e.repr (markedQuotientDirection F v w marked t (Pi.single i 1)) j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin t, A * B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (ha i) (he i j) (abs_nonneg _) hA
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)
  (e : Basis (Fin d) ℚ (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t))

variable [TopologicalSpace (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]
  [T2Space (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)]

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)

theorem realAffineMarkedSlope_zero (j : Fin s) : D.realAffineMarkedSlope t y 0 j = 0 := by
  apply Subtype.ext
  change (monomialLinearMap (0 : Fin t →₀ ℕ)).baseChange ℝ
    (∑ i, (0 : ℝ) • (y j i).val) = 0
  simp

theorem realAffineMarkedBase_shift_eval (a : Fin t → ℝ) (j : Fin s) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t a
          (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
            D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (D.realAffineMarkedBase t x y j))) =
      (x j).val + ∑ i, a i • (y j i).val := by
  apply realMarkedAffineShift_eval_affine
  intro b
  simpa only [← Rat.cast_smul_eq_qsmul ℝ] using D.realAffineMarkedBase_eval t x y j b

theorem commonAffineMarkedLift_shift_eval (a : Fin t → ℝ) (h n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
          D.coefficientFreeGenerator_mem_layer t a (D.commonAffineMarkedLift t x y 0 h n)) =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) • ((x j).val + ∑ i, a i • (y j i).val) := by
  have hz (j : Fin s) :
      realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (D.realAffineMarkedSlope t y 0 j) = 0 := by
    rw [D.realAffineMarkedSlope_zero t y j]
    exact (realMarkedPolynomialLift D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
      D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1).map_zero
  simp only [commonAffineMarkedLift, hz, smul_zero, add_zero,
    map_sum, LinearMap.map_smul_of_tower]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
    (D.realAffineMarkedBase_shift_eval t x y a j)

variable (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)

noncomputable def localPhaseMarkedLift (h : ZMod N) (n : ℤ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t :=
  realMarkedAffineShift D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
      (D.commonAffineMarkedLift t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)

theorem localPhaseMarkedLift_eval (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t 0).baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n) =
      ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
        ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  apply (D.commonAffineMarkedLift_shift_eval t x (fun j i => (m : ℝ)⁻¹ • y j i)
    (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  change ((m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) •
    ((m : ℝ)⁻¹ • (y j i).val) = _
  rw [smul_smul]
  apply congrArg (fun z : ℝ => z • (y j i).val)
  field_simp [hm0]

theorem localPhaseMarkedSmallElement_inv (h : ZMod N) :
    (D.localPhaseMarkedSmallElement t u c h₀ m h)⁻¹ =
      realMarkedParameterElement D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
        D.coefficientFreeGenerator_mem_layer t
          (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i) := by
  apply (realMarkedParameterElement_inv D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t
      (fun i => -(m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)).trans
  apply congrArg (realMarkedParameterElement D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent
    D.coefficientWeight_pos D.coefficientFreeGenerator_mem_layer t)
  funext i
  simp only [Pi.neg_apply, neg_mul, neg_neg]

theorem localPhaseMarkedLift_conjugation (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    conjugationCoord (D.localPhaseMarkedSmallElement t u c h₀ m h)⁻¹
      (((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n)
        (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)).coord) =
      (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
          (D.localPhaseMarkedLift t x y u c h₀ m h n) := by
  apply (congrArg (fun z => conjugationCoord z _)
    (D.localPhaseMarkedSmallElement_inv t u c h₀ m h)).trans
  apply (congrArg (conjugationCoord _)
    (D.commonAffineMarkedOrbit_eval t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)).trans
  exact realMarkedAffineShift_conjugation D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t hs
      (fun i => (m : ℝ) * affineCyclicTorusLocalLift u c h₀ h i)
      (D.commonAffineMarkedLift t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n)

theorem localPhaseMarkedOrbit_lift_factorization (hs : 1 ≤ s) (h : ZMod N) (n : ℤ) :
    (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) n) (D.localPhaseMarkedOrbit t x y u c h₀ m) *
        (D.scaledLocalAffineCorrectingElement t u c h₀ m h)⁻¹ =
      D.localPhaseMarkedSmallElement t u c h₀ m h *
        ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ := by
  let ε := D.localPhaseMarkedSmallElement t u c h₀ m h
  let g := (D.markedQuotientMultidegree t).realification.polynomialOrbitEval
    (correlationInput (h.val : ℤ) n)
    (D.commonAffineMarkedOrbit t x (fun j i => (m : ℝ)⁻¹ • y j i) 0)
  have hg : ε⁻¹ * g * ε =
      ⟨(lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
          (D.localPhaseMarkedLift t x y u c h₀ m h n)⟩ := by
    apply NilpotentLieBCHGroup.ext
    simpa only [conjugationCoord, inv_inv] using D.localPhaseMarkedLift_conjugation t x y u c h₀ m hs h n
  apply (D.localPhaseMarkedOrbit_right_normalization t x y u c h₀ m h n).trans
  calc
    g * ε = ε * (ε⁻¹ * g * ε) := by simp only [mul_assoc, mul_inv_cancel_left]
    _ = _ := congrArg (ε * ·) hg

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

theorem markedQuotientPhase_real_map (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedQuotientPhase F v w marked t).toLinearMap.baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap.baseChange ℝ z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedShiftTranslate_phase (a : Fin t → ℚ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
        ((markedShiftTranslate F v w marked hw hv t a).baseChange ℝ z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c z => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realMarkedAffineShift_phase (a : Fin t → ℝ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra F v w marked t) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
        (realMarkedAffineShift F v w marked hw hv t a z) =
      (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ z := by
  rw [realMarkedAffineShift_apply F v w marked hw hv t a z]
  simp only [map_add, map_sum, map_smul, map_sub, realMarkedShiftTranslate_phase,
    sub_self, smul_zero, Finset.sum_const_zero, add_zero]

theorem realMarkedPolynomialLift_phase (d k l : ℕ) (hd : d ≠ 0)
    (z : (markedPolynomialLayer (σ := Fin t) v w marked d k l).baseChange ℝ) :
    (markedShiftPhase F v w marked t).toLinearMap.baseChange ℝ
      (realMarkedPolynomialLift F v w marked hw hv t d k l z) = 0 := by
  have hker : markedShiftBiLayer F v w marked t k d ≤
      LinearMap.ker (markedShiftPhase F v w marked t).toLinearMap := by
    intro p hp
    exact hp.2 (Or.inl hd)
  have hz := Submodule.baseChange_mono ℝ hker (realMarkedPolynomialLift_mem F v w marked hw hv t d k l z)
  rwa [realification_ker, LinearMap.mem_ker] at hz

end Erdos3

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P) (t : ℕ)

noncomputable def markedDependentEvaluation (a : Fin t → ℚ) :
    MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t →ₗ[ℚ] D.DependentQuotient :=
  markedBaseEvaluation D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a

theorem markedDependentEvaluation_real_map (a : Fin t → ℚ)
    (z : ℝ ⊗[ℚ] markedShiftSubalgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t) :
    (D.markedDependentEvaluation t a).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ z) =
      D.dependentQuotientMap.toLinearMap.baseChange ℝ
        ((markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t a).baseChange ℝ z) :=
  markedBaseEvaluation_real_map D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t (D.dependentWordIdeal 0 2 0) le_rfl a z

theorem localPhaseMarkedLift_base_projection
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (hm : 0 < m) (h : ZMod N) (n : ℤ) :
    (D.markedDependentEvaluation t 0).baseChange ℝ
        ((lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
          D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
            (D.localPhaseMarkedLift t x y u c h₀ m h n)) =
      D.dependentQuotientMap.toLinearMap.baseChange ℝ
        (∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
          ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) :=
  (D.markedDependentEvaluation_real_map t 0 _).trans
    (congrArg (D.dependentQuotientMap.toLinearMap.baseChange ℝ)
      (D.localPhaseMarkedLift_eval t x y u c h₀ m hm h n))

theorem commonAffineMarkedLift_phase
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u : Fin t → ℝ) (h n : ℤ) :
    (markedShiftPhase D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t).toLinearMap.baseChange ℝ
        (D.commonAffineMarkedLift t x y u h n) = 0 := by
  simp only [commonAffineMarkedLift, map_sum, LinearMap.map_smul_of_tower, map_add]
  apply Finset.sum_eq_zero
  intro j _
  have hb := realMarkedPolynomialLift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 0 1 (by omega) (D.realAffineMarkedBase t x y j)
  have hs := realMarkedPolynomialLift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t (j.val + 1) 1 1 (by omega) (D.realAffineMarkedSlope t y u j)
  apply (congrArg₂ (fun a b : ℝ ⊗[ℚ] RationalTorus.Algebra t =>
    (n : ℚ) ^ (j.val + 1) • (a + (h : ℚ) • b)) hb hs).trans
  simp only [smul_zero, add_zero]

theorem localPhaseMarkedLift_pure
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ) (h : ZMod N) (n : ℤ) :
    (lieQuotientMap (markedShiftSecondIdeal D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t)).toLinearMap.baseChange ℝ
        (D.localPhaseMarkedLift t x y u c h₀ m h n) ∈
      (markedQuotientPolynomialAlgebra D.coefficientFreeFiltration D.coefficientFreeGenerator
        D.coefficientWeight D.coefficientIsDependent t).toSubmodule.baseChange ℝ := by
  change _ ∈ (LinearMap.ker (markedQuotientPhase D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t).toLinearMap).baseChange ℝ
  rw [realification_ker, LinearMap.mem_ker]
  apply (markedQuotientPhase_real_map D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t _).trans
  apply (realMarkedAffineShift_phase D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent D.coefficientWeight_pos
    D.coefficientFreeGenerator_mem_layer t _ _).trans
  exact D.commonAffineMarkedLift_phase t x (fun j i => (m : ℝ)⁻¹ • y j i) 0 h.val n

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped BigOperators TensorProduct NNReal

namespace RationalFilteredNilmanifold

end RationalFilteredNilmanifold

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N d : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (u c : Fin t → ℝ) (h₀ : ZMod N) (m : ℕ)
  (e : Basis (Fin d) ℚ (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
    D.coefficientWeight D.coefficientIsDependent t))

end NativeRankRelation.CommonData

end Erdos3

end

end OAI

end


