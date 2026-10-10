-- Prove2me | Definitions.Def_OAIErdos3B149
-- name    : OAIErdos3B149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T20:53:45.377981+00:00
-- url     : https://prove2.me/theorems/a5c02fb4-4f36-44f7-ae68-6ecd77da140f
-- title:
--   OpenAI Erdős-3 split, definitions bundle 150 of 169
-- statement:
--   Definitions bundle 150 of 169 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B148`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 150 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.exists_fixed_kernel_ambient_density_multiple`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicDiagonalCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicDiagonalCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.cyclicExchangeCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.diagonalSquareCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.diagonalSquareCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_cyclicDiagonalCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_cyclicExchangeCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_diagonalSquareCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_explicit_quadratic_root_equivalence`, `OAI.Erdos3.NativeMultidegreeNilcharacter.exists_rootCyclicCorrection_expansion`, `OAI.Erdos3.NativeMultidegreeNilcharacter.quadraticRoot`, `OAI.Erdos3.NativeMultidegreeNilcharacter.quadraticSquareTriple`, `OAI.Erdos3.NativeMultidegreeNilcharacter.quadraticSquareTriple_norm`, `OAI.Erdos3.NativeMultidegreeNilcharacter.rootCyclicCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.rootCyclicCorrection_mean_error`, `OAI.Erdos3.NativeMultidegreeNilcharacter.rootExchangeCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.wrappedDiagonalCorrection`, `OAI.Erdos3.NativeMultidegreeNilcharacter.wrappedDiagonalCorrection_mean_error`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval_sub_frozenSpatialEval`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenSpatialEval`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenTorus`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenTorus_lipschitz`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.frozenTorus_spatial_error`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.norm_frozenTorus_le`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedMixedSiteFactor`, `OAI.Erdos3.VectorPolynomial.allocatedBufferedSiteChartFactor`, `OAI.Erdos3.VectorPolynomial.allocatedFullAmbientSiteCoordinates`, `OAI.Erdos3.VectorPolynomial.allocatedFullMixedSiteValue`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceLip`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleFullSliceMap`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleTailNoise`, `OAI.Erdos3.VectorPolynomial.allocatedProductGridRadius`, `OAI.Erdos3.VectorPolynomial.allocatedProductGridRadius_pos`, `OAI.Erdos3.VectorPolynomial.allocatedProductGridRadius_recovery_budget`, `OAI.Erdos3.VectorPolynomial.allocatedProductGridRadius_source_budget`, `OAI.Erdos3.VectorPolynomial.allocatedProductIdealSiteRadius`, `OAI.Erdos3.VectorPolynomial.allocatedProductIdealSiteRadius_dominates`, `OAI.Erdos3.VectorPolynomial.allocatedProductIdealSiteRadius_one_le`, `OAI.Erdos3.VectorPolynomial.allocatedProductSiteCutoff`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialLateLog`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialLateLog_nonneg`, `OAI.Erdos3.VectorPolynomial.canonicalCoefficientDeckPeriodCap_le_exp`, `OAI.Erdos3.VectorPolynomial.canonicalPeriod_primitive_bounds`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientSiteEvaluation`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientSiteSection`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientSiteSection_lipschitz`, `OAI.Erdos3.VectorPolynomial.coefficientAmbientSiteSection_residual`, `OAI.Erdos3.VectorPolynomial.coefficientResidualAmbientDensity`, `OAI.Erdos3.VectorPolynomial.coefficientResidualAmbientDensity_bounds`, `OAI.Erdos3.VectorPolynomial.coefficientResidualAmbientDensity_eq`, `OAI.Erdos3.VectorPolynomial.coefficientResidualAmbientDensity_lipschitz`, `OAI.Erdos3.VectorPolynomial.coefficientSectionAmbientDensity`, `OAI.Erdos3.VectorPolynomial.coefficientSectionAmbientDensity_bounds`, `OAI.Erdos3.VectorPolynomial.coefficientSectionAmbientDensity_eq`, `OAI.Erdos3.VectorPolynomial.coefficientSectionAmbientDensity_lipschitz`, `OAI.Erdos3.VectorPolynomial.exists_allocatedSpatialLateLog_bound`, `OAI.Erdos3.VectorPolynomial.periodFunctionLabelCard_le_exp`, `OAI.Erdos3.VectorPolynomial.singleSiteFromLayered`, `OAI.Erdos3.cyclicSecondDifference`, `OAI.Erdos3.cyclicSecondDifference_branches`, `OAI.Erdos3.finiteChoiceLeafInput_get`, `OAI.Erdos3.finiteChoiceLeafInput_of_not_mem`, `OAI.Erdos3.integerSecondDifference`, `OAI.Erdos3.integerSecondDifference_norm`, `OAI.Erdos3.mixedChoiceAssignmentEquiv`, `OAI.Erdos3.mixedChoiceSample`, `OAI.Erdos3.mixedChoiceSample_leaf`, `OAI.Erdos3.mixedChoiceSample_replica`, `OAI.Erdos3.mixedChoiceSample_sum`, `OAI.Erdos3.norm_smoothed_branch_error`, `OAI.Erdos3.norm_unit_vector_exchange_error`, `OAI.Erdos3.selectedJointFiniteLaw_site_excess`, `OAI.Erdos3.smoothedSecondDifference`, `OAI.Erdos3.smoothedSecondDifference_mean_error`, `_private.Probability.CommonSectionAmbientDensityMultiple.0.OAI.Erdos3.VectorPolynomial.unitAddCircle_coe_sum`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B052
import Definitions.Def_OAIErdos3B129
import Definitions.Def_OAIErdos3B132
import Definitions.Def_OAIErdos3B138

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteChoiceLeafCoordinates
namespace OAI

section

namespace Erdos3

variable {σ : Type*} [DecidableEq σ] {n : ℕ}

theorem finiteChoiceLeafInput_of_not_mem (l : List σ) :
    ∀ (v : Fin l.length → Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ) (j : σ),
      j ∉ l → finiteChoiceLeafInput l v x j = x (0, j) := by
  induction l with
  | nil => intro v x j _; rfl
  | cons i l ih =>
      intro v x j hj
      simp only [List.mem_cons, not_or] at hj
      rw [finiteChoiceLeafInput, ih (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) j hj.2]
      simp [finiteChoiceReplaceInput, finiteChoiceReplaceIndex, hj.1]

theorem finiteChoiceLeafInput_get (l : List σ) :
    l.Nodup → ∀ (v : Fin l.length → Fin (n + 1)) (x : (Fin (n + 1) × σ) → ℤ)
      (j : Fin l.length), finiteChoiceLeafInput l v x (l.get j) = x (v j, l.get j) := by
  induction l with
  | nil => intro _ v x j; exact Fin.elim0 j
  | cons i l ih =>
      intro hl v x j
      obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
      refine Fin.cases ?_ (fun k => ?_) j
      · change finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) i =
          x (v 0, i)
        rw [finiteChoiceLeafInput_of_not_mem l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) i hi]
        simp [finiteChoiceReplaceInput, finiteChoiceReplaceIndex]
      · change finiteChoiceLeafInput l (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) (l.get k) =
          x (v k.succ, l.get k)
        rw [ih hl (Fin.tail v) (finiteChoiceReplaceInput i (v 0) x) k]
        have hki : l.get k ≠ i := by
          intro heq
          apply hi
          rw [← heq]
          exact List.get_mem l k
        change x (if (v k.succ, l.get k) = (0, i) then (v 0, i) else (v k.succ, l.get k)) = _
        rw [if_neg (fun h => hki (congrArg Prod.snd h))]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.MixedAssignmentSampling
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedChoiceAssignmentEquiv (s n : ℕ) :
    (Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) ≃ (Fin s → Fin (n + 1)) where
  toFun v j := v (Fin.cast (mixedRepeatedCoordinates_length s).symm j)
  invFun v j := v (Fin.cast (mixedRepeatedCoordinates_length s) j)
  left_inv v := by funext j; rfl
  right_inv v := by funext j; rfl

def mixedChoiceSample {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (j : Fin (n + 1) × MixedReplicatedIndex s) : ℤ :=
  correlationInput h (y j.1) j.2.1

theorem mixedChoiceSample_replica {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (a : Fin (n + 1)) (j : Fin s) : mixedChoiceSample h y (a, mixedReplica j) = y a := rfl

theorem mixedChoiceSample_sum {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ) :
    finiteChoiceCoordinateInput (mixedRepeatedCoordinates s) (mixedChoiceSample h y) =
      mixedReplicatedInput h (fun _ : Fin s => ∑ a, y a) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head]
    simp [finiteChoiceCoordinateInput, mem_mixedRepeatedCoordinates, mixedHead,
      mixedChoiceSample, correlationInput]
  · rw [mixedReplicatedInput_replica]
    have hi : mixedReplica i ∈ mixedRepeatedCoordinates s :=
      (mem_mixedRepeatedCoordinates s _).mpr rfl
    simp only [finiteChoiceCoordinateInput, hi, ite_true, mixedChoiceSample_replica]

theorem mixedChoiceSample_leaf {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (v : Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) :
    finiteChoiceLeafInput (mixedRepeatedCoordinates s) v (mixedChoiceSample h y) =
      mixedReplicatedInput h (fun j => y (mixedChoiceAssignmentEquiv s n v j)) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head]
    have hnot : mixedHead s ∉ mixedRepeatedCoordinates s := by
      simp [mem_mixedRepeatedCoordinates, mixedHead]
    rw [finiteChoiceLeafInput_of_not_mem _ v _ _ hnot]
    rfl
  · rw [mixedReplicatedInput_replica]
    let k : Fin (mixedRepeatedCoordinates s).length := Fin.cast (mixedRepeatedCoordinates_length s).symm i
    have H := finiteChoiceLeafInput_get (mixedRepeatedCoordinates s)
      (mixedRepeatedCoordinates_nodup s) v (mixedChoiceSample h y) k
    rw [mixedRepeatedCoordinates_get] at H
    have hk : Fin.cast (mixedRepeatedCoordinates_length s) k = i := rfl
    rw [hk, mixedChoiceSample_replica] at H
    exact H

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalCyclicDifference
namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_explicit_quadratic_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C) W.eval
        (tensorVector ((W.rationalDilation (1 / 2)).tensorPower 2).eval 2) := by
  have hsum : (∑ i, mixedCorrelationDegree 1 i) = 2 := by decide
  have hpos : 1 ≤ ∑ i, mixedCorrelationDegree 1 i := by rw [hsum]; norm_num
  obtain ⟨A, _, hdilation⟩ := exists_dilation_degree_equivalence (mixedCorrelationDegree 1) hpos 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 6 * (X + 1) + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hbound : (p + A) ^ A + 6 * (p + 1) + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith
  have hAr : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hdimBound : 2 * tensorPowerBudget 2 p ≤ (p + C) ^ C := by
    norm_num [tensorPowerBudget]
    linarith
  let V := W.rationalDilation (1 / 2)
  let R := V.tensorPower 2
  have hleft (i : Fin W.outputDim) (x : Fin 2 → ℤ) :
      W.eval i x = integerDilationVector V.eval 2 i x :=
    (W.rationalDilation_eval_rescaled (1 / 2) 2 (by norm_num) i x).symm
  have hright (b : Fin 2 → Fin R.outputDim) (x : Fin 2 → ℤ) :
      tensorVector R.eval 2 b x =
        signedTensorVector V.eval ((2 : ℤ) ^ ∑ j, mixedCorrelationDegree 1 j)
          (rootTensorIndex W.outputDim 2 (∑ j, mixedCorrelationDegree 1 j) hpos b) x := by
    exact V.tensorPower_tensor_eval 2 (∑ j, mixedCorrelationDegree 1 j) hpos b x
  have hdim : (Fintype.card (Fin 2 → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 2 p) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp (2 * tensorPowerBudget 2 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 2 p) 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have E := (hdilation V).of_coordinate_maps W.eval (tensorVector R.eval 2) id
    (rootTensorIndex W.outputDim 2 (∑ j, mixedCorrelationDegree 1 j) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr
  simpa only [hsum, Nat.reduceSub] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_unit_vector_exchange_error {I : Type*} [Fintype I]
    (v : I → ℂ) (hv : ∑ i, ‖v i‖ ^ 2 = 1) (hcap : ∀ i, ‖v i‖ ≤ 1)
    (a : ℂ) (g : I → ℂ) :
    ‖a - ∑ i, v i * star (g i)‖ ≤ ∑ i, ‖star a * v i - g i‖ := by
  have hsum : (∑ i, v i * star (star a * v i)) = a := by
    calc
      _ = ∑ i, (a * star (v i)) * v i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [star_mul, star_star]
        ring
      _ = a := (complex_unit_vector_resolution v hv a).symm
  have heq : a - ∑ i, v i * star (g i) = ∑ i, v i * star (star a * v i - g i) := by
    simp only [star_sub, mul_sub, Finset.sum_sub_distrib, hsum]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _) (hcap i)

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticSquareTriple (a : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  star ((W.eval a.1 (correlationInput (x 0) (x 1)) *
    W.eval a.2.1 (correlationInput (x 0) (x 1))) * W.eval a.2.2 (fun _ => x 0))

noncomputable def diagonalSquareCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
    star (G b.1 j x)

theorem diagonalSquareCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ZMod N) :
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.diagonalSquareCorrection G a b (fun z => ((x z).val : ℤ))‖ ≤
      ∑ j, ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G b.1 j (fun z => ((x z).val : ℤ))‖ := by
    let z := fun i => ((x i).val : ℤ)
    let c := (W.quadraticDiagonalDerivative a z * W.eval b.2.1 (correlationInput (z 0) (z 1))) *
      W.eval b.2.2 (fun _ => z 0)
    have hc : ‖c‖ ≤ 1 := by
      simp only [c, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _) (W.quadraticDiagonalDerivative_norm a z)).trans
          (W.norm_eval _ _))).trans (W.norm_eval _ _)
    have htarget : W.quadraticDiagonalDerivative a z * star (W.quadraticSquareTriple b z) =
        c * W.eval b.1 (correlationInput (z 0) (z 1)) := by
      simp only [quadraticSquareTriple, star_star, c]
      ring
    have hsum : W.diagonalSquareCorrection G a b z =
        c * ∑ j, W.eval j (correlationInput (z 1) (z 0)) * star (G b.1 j z) := by
      unfold diagonalSquareCorrection
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [quadraticMixedTriple, star_star, c]
      ring
    change ‖W.quadraticDiagonalDerivative a z * star (W.quadraticSquareTriple b z) -
      W.diagonalSquareCorrection G a b z‖ ≤ _
    rw [htarget, hsum, ← mul_sub, norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
    exact norm_unit_vector_exchange_error
      (fun j => W.eval j (correlationInput (z 1) (z 0))) (W.unit_eval _) (fun j => W.norm_eval j _)
      (W.eval b.1 (correlationInput (z 0) (z 1))) (fun j => G b.1 j z)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ j, ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G b.1 j (fun z => ((x z).val : ℤ))‖ := Finset.expect_le_expect (fun x _ => hpoint x)
    _ = ∑ j, 𝔼 x : Fin 2 → ZMod N,
        ‖W.antisymmetricKernel b.1 j ((x 0).val : ℤ) ((x 1).val : ℤ) -
          G b.1 j (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _j : Fin W.outputDim, ε := Finset.sum_le_sum (fun j _ => herr b.1 j)
    _ = _ := by simp

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem norm_smoothed_branch_error (c w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1)
    (a b u v : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖((1 - c : ℝ) : ℂ) * a + (c : ℂ) * b -
      (((1 - w : ℝ) : ℂ) * u + (w : ℂ) * v)‖ ≤
      ‖a - u‖ + ‖b - v‖ + 2 * |c - w| := by
  have heq : ((1 - c : ℝ) : ℂ) * a + (c : ℂ) * b -
      (((1 - w : ℝ) : ℂ) * u + (w : ℂ) * v) =
      (((1 - w : ℝ) : ℂ) * (a - u) + (w : ℂ) * (b - v)) +
        ((c - w : ℝ) : ℂ) * (b - a) := by push_cast; ring
  have hba : ‖b - a‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  rw [heq]
  calc
    _ ≤ ‖((1 - w : ℝ) : ℂ) * (a - u)‖ + ‖(w : ℂ) * (b - v)‖ +
        ‖((c - w : ℝ) : ℂ) * (b - a)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (1 - w) * ‖a - u‖ + w * ‖b - v‖ + |c - w| * ‖b - a‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 - w), abs_of_nonneg hw.1]
    _ ≤ ‖a - u‖ + ‖b - v‖ + |c - w| * 2 :=
      add_le_add (add_le_add (mul_le_of_le_one_left (norm_nonneg _) (by linarith))
        (mul_le_of_le_one_left (norm_nonneg _) hw.2))
        (mul_le_mul_of_nonneg_left hba (abs_nonneg _))
    _ = _ := by ring

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

theorem quadraticSquareTriple_norm (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.quadraticSquareTriple b x‖ ≤ 1 := by
  simp only [quadraticSquareTriple, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
      (W.norm_eval _ _))).trans (W.norm_eval _ _)

noncomputable def wrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.diagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def cyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.wrappedDiagonalCorrection N F a b x

theorem wrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.wrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.wrappedDiagonalDerivative N a x * star (W.quadraticSquareTriple b x) -
        W.wrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.quadraticDiagonalDerivative (a.1, k) x * star (W.quadraticSquareTriple b x) -
        F (a.1, k) b x‖ := by
    have heq : W.wrappedDiagonalDerivative N a x * star (W.quadraticSquareTriple b x) -
        W.wrappedDiagonalCorrection N F a b x =
        ∑ k, W.diagonalWrapCoefficient N a.2 k x *
          (W.quadraticDiagonalDerivative (a.1, k) x * star (W.quadraticSquareTriple b x) -
            F (a.1, k) b x) := by
      rw [W.wrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [wrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.diagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.quadraticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.quadraticDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem cyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cyclicDiagonalDerivative a x * star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))) -
        W.cyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.quadraticDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))))
    (W.wrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.quadraticSquareTriple b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.wrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.quadraticDiagonalDerivative_norm a _)).trans (W.quadraticSquareTriple_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.wrappedDiagonalDerivative_norm N a _)).trans (W.quadraticSquareTriple_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.cyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.wrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [cyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem exists_cyclicDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (Fin W.outputDim × Fin W.outputDim × Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
          ((p + q + e + C) ^ C) (W.cyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_diagonalWrapCoefficient_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 6
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + 6
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have her : e + 4 ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
      (W.wrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 t
      (fun x => ∑ k, W.diagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := (Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.wrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.cyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, cyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end NativeMultidegreeNilcharacter

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def integerSecondDifference (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ)
    (x : Fin 2 → ℤ) : ℂ := u x * star (v ![x 0, x 1 + k])

noncomputable def cyclicSecondDifference {N : ℕ} (u v : (Fin 2 → ℤ) → ℂ)
    (k : ZMod N) (h : ℤ) (n : ZMod N) : ℂ :=
  u ![h, (n.val : ℤ)] * star (v ![h, ((n + k).val : ℤ)])

noncomputable def smoothedSecondDifference (N : ℕ) (δ : ℝ≥0)
    (u v : (Fin 2 → ℤ) → ℂ) (k : ℤ) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ ![k, x 1] : ℂ)) * integerSecondDifference u v k x +
    (smoothCyclicCarry N δ ![k, x 1] : ℂ) * integerSecondDifference u v (k - N) x

theorem integerSecondDifference_norm (u v : (Fin 2 → ℤ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (k : ℤ) (x : Fin 2 → ℤ) :
    ‖integerSecondDifference u v k x‖ ≤ 1 := by
  rw [integerSecondDifference, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hu _)).trans (hv _)

theorem cyclicSecondDifference_branches {N : ℕ} [NeZero N]
    (u v : (Fin 2 → ℤ) → ℂ) (k : ZMod N) (h : ℤ) (n : ZMod N) :
    cyclicSecondDifference u v k h n =
      (1 - (cyclicCarry k n : ℂ)) * integerSecondDifference u v k.val ![h, (n.val : ℤ)] +
        (cyclicCarry k n : ℂ) * integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)] := by
  have hval : ((n + k).val : ℤ) = (n.val : ℤ) + k.val -
      if N - k.val ≤ n.val then (N : ℤ) else 0 := by
    simpa only [add_comm n k] using cyclic_representative_add k n
  have hk := k.val_lt
  by_cases hw : N ≤ k.val + n.val
  · have hcut : N - k.val ≤ n.val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cyclicSecondDifference, integerSecondDifference, Matrix.cons_val_zero, Matrix.cons_val_one,
      hval, if_pos hcut]
    rw [add_sub_assoc]
  · have hcut : ¬N - k.val ≤ n.val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cyclicSecondDifference, integerSecondDifference, Matrix.cons_val_zero, Matrix.cons_val_one,
      hval, if_neg hcut]

theorem smoothedSecondDifference_mean_error {N : ℕ} [NeZero N]
    (δ : ℝ≥0) (hδ : 0 < δ) (u v : (Fin 2 → ℤ) → ℂ)
    (hu : ∀ x, ‖u x‖ ≤ 1) (hv : ∀ x, ‖v x‖ ≤ 1) (k : ZMod N) (h : ℤ) :
    (𝔼 n : ZMod N, ‖cyclicSecondDifference u v k h n -
      smoothedSecondDifference N δ u v k.val ![h, (n.val : ℤ)]‖) ≤
        12 * (δ : ℝ) + 2 / N := by
  have hp (n : ZMod N) : ‖cyclicSecondDifference u v k h n -
      smoothedSecondDifference N δ u v k.val ![h, (n.val : ℤ)]‖ ≤
        2 * |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| := by
    have hh := norm_smoothed_branch_error (cyclicCarry k n)
      (smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]) (circleCarryCutoff_range δ _)
      (integerSecondDifference u v k.val ![h, (n.val : ℤ)])
      (integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)])
      (integerSecondDifference u v k.val ![h, (n.val : ℤ)])
      (integerSecondDifference u v ((k.val : ℤ) - N) ![h, (n.val : ℤ)])
      (integerSecondDifference_norm u v hu hv _ _)
      (integerSecondDifference_norm u v hu hv _ _)
    simpa only [Complex.ofReal_sub, Complex.ofReal_one, sub_self, norm_zero, zero_add,
      ← cyclicSecondDifference_branches, smoothedSecondDifference, Matrix.cons_val_one,
      Matrix.cons_val_zero] using hh
  calc
    _ ≤ 𝔼 n : ZMod N,
        2 * |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]| :=
      Finset.expect_le_expect (fun n _ => hp n)
    _ = 2 * (𝔼 n : ZMod N,
        |cyclicCarry k n - smoothCyclicCarry N δ ![(k.val : ℤ), (n.val : ℤ)]|) :=
      (Finset.mul_expect _ _ _).symm
    _ ≤ 2 * (6 * (δ : ℝ) + 1 / N) :=
      mul_le_mul_of_nonneg_left (smoothCyclicCarry_fixed_shift_mean_error δ hδ k) (by norm_num)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

theorem exists_diagonalSquareCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p), 0 ≤ q →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
        ((p + q + C) ^ C) (W.diagonalSquareCorrection G a b)) := by
  obtain ⟨A, _, hdiag⟩ := exists_quadratic_diagonal_derivative_equivalence
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C B) ^ B + X)
  refine ⟨C, hC, ?_⟩
  intro p q W hq G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q
  let r := (v + A) ^ A + v + 2
  have hv : 0 ≤ v := add_nonneg hp hq
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    dsimp [r, v]
    linarith
  have hAr : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; linarith
  have hcost : (r + B) ^ B + p ≤ (p + q + C) ^ C := by
    have hh : (r + B) ^ B + v ≤ (p + q + C) ^ C := by
      simpa [X, R, r, v, Polynomial.eval₂_pow] using hbudget v hv
    dsimp [v] at hh
    linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _j : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterm (j : Fin W.outputDim) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((r + B) ^ B)
        (fun x => (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
          star (G b.1 j x))) :=
    hmul hr ((Classical.choice ((hdiag W).expansion a (j, b.2))).mono hAr)
      ((Classical.choice (hG b.1 j)).conjugate.mono hqr)
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (hterm j))
    (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hcost
  change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + C) ^ C)
    (fun x => ∑ j, (W.quadraticDiagonalDerivative a x * star (W.quadraticMixedTriple (j, b.2) x)) *
      star (G b.1 j x)))
  exact ⟨by simpa only [one_mul] using E⟩

theorem exists_cyclicExchangeCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + e + C) ^ C)
        (W.cyclicDiagonalCorrection N δ (W.diagonalSquareCorrection G) a b)) := by
  obtain ⟨A, _, hdiag⟩ := exists_diagonalSquareCorrection_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cyclicDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + (X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : (p + q + A) ^ A ≤ (p + q + e + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (p + (p + q + A) ^ A + e + B) ^ B ≤ (p + q + e + C) ^ C := by
    have hh : (p + q + e + (p + q + e + A) ^ A + B) ^ B ≤ (p + q + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + q + e) (by positivity)
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by positivity)
    linarith
  obtain ⟨E⟩ := hcyclic W N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.diagonalSquareCorrection G) (hdiag W hq G hG) a b
  exact ⟨E.mono hb⟩

theorem cyclicExchangeCorrection_mean_error {p ε : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel a b ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G a b (fun k => ((x k).val : ℤ))‖) ≤ ε) (a b) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cyclicDiagonalDerivative a x * star (W.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        W.cyclicDiagonalCorrection N δ (W.diagonalSquareCorrection G) a b
          (fun k => ((x k).val : ℤ))‖) ≤
      (W.outputDim + 1) * (W.outputDim * ε) + 12 * (δ : ℝ) + 2 / N :=
  W.cyclicDiagonalCorrection_mean_error δ hδ (W.diagonalSquareCorrection G)
    (W.diagonalSquareCorrection_mean_error G herr) a b

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def quadraticRoot :
    NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) (tensorPowerBudget 2 p) :=
  (W.rationalDilation (1 / 2)).tensorPower 2

noncomputable def rootExchangeCorrection
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  (W.rationalDilation (1 / 2)).tensorSquareExchangeCorrection (W.halfDilationExchangeCorrection G)

noncomputable def rootCyclicCorrection (N : ℕ) (δ : ℝ≥0)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) :=
  W.quadraticRoot.cyclicDiagonalCorrection N δ
    (W.quadraticRoot.diagonalSquareCorrection (W.rootExchangeCorrection G))

theorem rootCyclicCorrection_mean_error {N : ℕ} [NeZero N] (δ : ℝ≥0) (hδ : 0 < δ)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) {ε : ℝ}
    (hcap : ∀ i j (x : Fin 2 → ZMod N), ‖G i j (fun k => ((x k).val : ℤ))‖ ≤ 1)
    (herr : ∀ i j, (𝔼 x : Fin 2 → ZMod N,
      ‖W.antisymmetricKernel i j ((x 0).val : ℤ) ((x 1).val : ℤ) -
        G i j (fun k => ((x k).val : ℤ))‖) ≤ ε) (a b) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.quadraticRoot.cyclicDiagonalDerivative a x *
          star (W.quadraticRoot.quadraticSquareTriple b (fun k => ((x k).val : ℤ))) -
        W.rootCyclicCorrection N δ G a b (fun k => ((x k).val : ℤ))‖) ≤
      (W.quadraticRoot.outputDim + 1) *
        (W.quadraticRoot.outputDim * ((1 + (W.outputDim : ℝ) ^ 2) * (4 * (W.outputDim : ℝ) ^ 2 * ε))) +
        12 * (δ : ℝ) + 2 / N := by
  exact W.quadraticRoot.cyclicExchangeCorrection_mean_error δ hδ (W.rootExchangeCorrection G)
    (W.explicit_half_root_exchange_mean_error G hcap herr) a b

theorem exists_rootCyclicCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (δ : ℝ≥0),
      0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
      (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 q (G a b))) →
      ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + q + e + C) ^ C)
        (W.rootCyclicCorrection N δ G a b)) := by
  obtain ⟨A, _, hroot⟩ := exists_explicit_half_root_exchange_expansion
  obtain ⟨B, _, hcyclic⟩ := exists_cyclicExchangeCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * (X + 1) + (X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv G hG a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hA : (p + q + A) ^ A ≤ (v + A) ^ A :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have hbound : (tensorPowerBudget 2 p + (p + q + A) ^ A + e + B) ^ B ≤
      (p + q + e + C) ^ C := by
    have hh : (3 * (v + 1) + (v + A) ^ A + v + B) ^ B ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hh
    apply pow_le_pow_left₀ (by unfold tensorPowerBudget; positivity)
    norm_num only [tensorPowerBudget, Nat.cast_ofNat] at *
    dsimp [v] at *
    linarith
  obtain ⟨E⟩ := hcyclic W.quadraticRoot N δ hδ (by positivity : 0 ≤ (p + q + A) ^ A) he hinv
    (W.rootExchangeCorrection G) (hroot W hq G hG) a b
  exact ⟨E.mono hbound⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SelectedJointSiteDomination
namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical

theorem selectedJointFiniteLaw_site_excess
    {K I X T : Type*} [Fintype K] [Fintype I]
    [Fintype X] [Nonempty X] [Fintype T] [Nonempty T]
    (A : Finset (I → ℤ)) (hA : A.Nonempty)
    (modulus : I → ℕ) (cells : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (D : (I → ℤ) → (Option K × I → ℤ) → ℝ) (hD : ∀ a z, 0 ≤ D a z)
    (htotal : 0 < selectedJointDensityMass A modulus cells W D)
    (hlower : 1 / 2 ≤ selectedJointDensityMass A modulus cells W D)
    (e : X → I → ℝ) (he : Function.Injective e)
    (root : T → K → ℤ)
    (F : (A × rectangularWeightIndices 0 W 1) → T → X)
    (hF : ∀ z t, e (F z t) = (fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val)
    (hcard : (Fintype.card X : ℝ) / A.card ≤ 2)
    {M ε : ℝ} (hM : 0 ≤ M)
    (hlocal : ∀ (a : I → ℤ) (t : T) (φ : (I → ℝ) → ℝ),
      (∀ u, φ u ∈ Set.Icc (0 : ℝ) 1) →
      (∑' z, (selectedResidueSmoothPMF modulus cells W hW hZ z).toReal *
        (φ ((fun i => (a i : ℝ)) + physicalAffineSite (root t) z) * D a z)) ≤
      M * (∑' z, (selectedResidueSmoothPMF modulus cells W hW hZ z).toReal *
        φ ((fun i => (a i : ℝ)) + physicalAffineSite (root t) z)) + ε) :
    (FiniteProbabilityWeights.uniform X).excessMass
      ((selectedJointFiniteLaw A hA modulus cells W hW hZ D hD htotal).siteLaw F)
      (4 * M) ≤ 2 * ε := by
  let : Nonempty A := hA.to_subtype
  let q := selectedResidueFiniteLaw modulus cells W hW hZ
  apply FiniteProbabilityWeights.siteLaw_excessMass_le_of_test_bound
  intro φ hφ t
  let ψ : (I → ℝ) → ℝ := fun u => φ (Function.invFun e u)
  have hψ (u) : ψ u ∈ Set.Icc (0 : ℝ) 1 := hφ _
  have hvalue (z : A × rectangularWeightIndices 0 W 1) :
      ψ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite (root t) z.2.val) = φ (F z t) := by
    rw [← hF z t]
    exact congrArg φ (Function.leftInverse_invFun he (F z t))
  have hinj (z : rectangularWeightIndices 0 W 1) :
      Function.Injective (fun a : A => F (a, z) t) := by
    intro a b hab
    have hc := congrArg e hab
    rw [hF, hF] at hc
    have hd := add_right_cancel hc
    apply Subtype.ext
    funext i
    exact_mod_cast congrFun hd i
  have hlocal' (a : A) :
      q.mean (fun z => D a.val z.val * φ (F (a, z) t)) ≤
        M * q.mean (fun z => φ (F (a, z) t)) + ε := by
    have h := hlocal a.val t ψ hψ
    rw [← selectedResidueFiniteLaw_mean, ← selectedResidueFiniteLaw_mean] at h
    have hv (z : rectangularWeightIndices 0 W 1) :
        ψ ((fun i => (a.val i : ℝ)) + physicalAffineSite (root t) z.val) = φ (F (a, z) t) :=
      hvalue (a, z)
    simpa only [hv, mul_comm] using h
  have hz : 0 < ((FiniteProbabilityWeights.uniform A).prod q).mean
      (fun z => D z.1.val z.2.val) := by
    change 0 < (selectedJointReference A hA modulus cells W hW hZ).mean _
    rw [selectedJointReference_densityMass]
    exact htotal
  have hl : 1 / 2 ≤ ((FiniteProbabilityWeights.uniform A).prod q).mean
      (fun z => D z.1.val z.2.val) := by
    change 1 / 2 ≤ (selectedJointReference A hA modulus cells W hW hZ).mean _
    rw [selectedJointReference_densityMass]
    exact hlower
  have h := FiniteProbabilityWeights.uniform_base_reweight_test_le q
    (fun z => D z.1.val z.2.val) (fun z => hD z.1.val z.2.val) hz
    (fun z => F z t) hinj φ (fun x => (hφ x).1) hM (by norm_num : (0 : ℝ) < 1 / 2)
    hl hlocal'
  change (selectedJointFiniteLaw A hA modulus cells W hW hZ D hD htotal).mean
    (fun z => φ (F z t)) ≤ _ at h
  apply h.trans
  have hn := (FiniteProbabilityWeights.uniform X).mean_nonneg (fun x => (hφ x).1)
  have hr : (Fintype.card X : ℝ) / Fintype.card A ≤ 2 := by simpa using hcard
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hM) hn
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.CommonSectionAmbientDensityMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
variable (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

noncomputable def coefficientResidualAmbientDensity
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) : ℝ :=
  ∫ y, f (z + coefficientAmbientTorus U
    (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ

omit [Fintype K] [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)]
  [IsProbabilityMeasure μ] in
theorem coefficientResidualAmbientDensity_eq
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (x : CoefficientTorus (K := K) U) :
    coefficientResidualAmbientDensity U R hR μ f (coefficientAmbientTorus U x) =
      linearQuotientAverage (coefficientIntegerLattice U) R hR μ
        (fun z => f (coefficientAmbientTorus U z)) x := by
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  funext t
  simp only [coefficientAmbientTorus, map_add, Pi.add_apply]

omit [Fintype K] [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem coefficientResidualAmbientDensity_bounds
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {C : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) C) (z) :
    coefficientResidualAmbientDensity U R hR μ f z ∈ Set.Icc (0 : ℝ) C := by
  have h0 : 0 ≤ coefficientResidualAmbientDensity U R hR μ f z :=
    integral_nonneg (fun y => (hf _).1)
  refine ⟨h0, ?_⟩
  have hn := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun y =>
      show ‖f (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))‖ ≤ C from
      by rw [Real.norm_of_nonneg (hf _).1]; exact (hf _).2))
  change ‖coefficientResidualAmbientDensity U R hR μ f z‖ ≤ C * μ.real Set.univ at hn
  simpa only [probReal_univ, mul_one, Real.norm_of_nonneg h0] using hn

theorem coefficientResidualAmbientDensity_lipschitz
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hfb : ∀ z, ‖f z‖ ≤ C) :
    LipschitzWith L (coefficientResidualAmbientDensity U R hR μ f) := by
  have hRc := linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hR
    R.continuous_of_finiteDimensional
  have hi (z : CoefficientAmbientIndex K J → UnitAddCircle) :
      Integrable (fun y => f (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))) μ := by
    apply Integrable.of_bound (C := C)
    · exact (hf.continuous.comp (continuous_const.add
        ((coefficientAmbientTorus_continuous U).comp hRc))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun _ => hfb _)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  change ‖(∫ y, f (z + coefficientAmbientTorus U
      (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ) -
    ∫ y, f (w + coefficientAmbientTorus U
      (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) ∂μ‖ ≤ _
  rw [← integral_sub (hi z) (hi w)]
  calc
    _ ≤ ((L : ℝ) * dist z w) * μ.real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards [] with y
      have h := hf.dist_le_mul (z + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))
        (w + coefficientAmbientTorus U
        (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y))
      rw [dist_add_right] at h
      exact h
    _ = _ := by rw [probReal_univ, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal

theorem unitAddCircle_coe_sum {A : Type*} [Fintype A] (a : A → ℝ) :
    ((∑ t, a t : ℝ) : UnitAddCircle) = ∑ t, (a t : UnitAddCircle) :=
  map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) a Finset.univ

variable {K S : Type*} [Fintype K] [Fintype S] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def coefficientAmbientSiteSection
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    (z : JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle) :
    CoefficientAmbientIndex K J → UnitAddCircle :=
  fun t => ∑ s, T t.1.1 t.1.2 s • z ⟨t.1.1, s, t.2⟩

noncomputable def coefficientAmbientSiteEvaluation (site : S → K → ℤ)
    (z : CoefficientAmbientIndex K J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle :=
  fun t => ∑ e, boundedSiteMatrix (t.1.val + 1) site t.2.1 e • z ⟨⟨t.1, e⟩, t.2.2⟩

theorem coefficientAmbientSiteSection_lipschitz
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)
    {L : ℝ≥0} (hT : ∀ j e, ∑ s, ‖T j e s‖ ≤ L) :
    LipschitzWith L (coefficientAmbientSiteSection (J := J) T) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨⟨j, e⟩, i⟩
  calc
    _ ≤ ∑ s, dist (T j e s • z ⟨j,s,i⟩) (T j e s • w ⟨j,s,i⟩) := dist_sum_sum_le _ _ _
    _ ≤ ∑ s, ‖T j e s‖ * dist z w := by
      apply Finset.sum_le_sum
      intro s _
      rw [dist_eq_norm, ← smul_sub]
      exact (norm_zsmul_le _ _).trans (mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using dist_le_pi_dist z w ⟨j,s,i⟩) (norm_nonneg _))
    _ = (∑ s, ‖T j e s‖) * dist z w := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hT j e) dist_nonneg

variable (U : ∀ j, Submodule ℝ (J j → ℝ)) (site : S → K → ℤ) (q : ℕ)
variable (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) S ℤ)

local notation "R" => coefficientSiteResidual U site (fun _ => q) T
local notation "hR" => coefficientSiteResidual_preserves_lattice U site (fun _ => q) T

omit [∀ j, Fintype (J j)] in
theorem coefficientAmbientSiteSection_residual (x : CoefficientTorus (K := K) U) :
    coefficientAmbientSiteSection T (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x)) +
      coefficientAmbientTorus U (linearQuotientEndomorphism (coefficientIntegerLattice U) R hR x) =
    coefficientAmbientTorus U (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [quotientIntegerCover_mk]
  funext t
  rcases t with ⟨⟨j, e⟩, i⟩
  change (∑ s, T j e s • ∑ a, boundedSiteMatrix (j.val + 1) site s a •
    ((v ⟨j,a⟩).val i : UnitAddCircle)) +
      (((q : ℝ) * (v ⟨j,e⟩).val i -
        (matrixModuleAction (fun a s => (T j a s : ℝ))
          (matrixModuleAction (fun s a => (boundedSiteMatrix (j.val + 1) site s a : ℝ))
            (coefficientLayerArray U j v)) e).val i : ℝ) : UnitAddCircle) =
      (((q : ℝ) * (v ⟨j,e⟩).val i : ℝ) : UnitAddCircle)
  have he : ((matrixModuleAction (fun a s => (T j a s : ℝ))
      (matrixModuleAction (fun s a => (boundedSiteMatrix (j.val + 1) site s a : ℝ))
        (coefficientLayerArray U j v)) e).val i : UnitAddCircle) =
      ∑ s, T j e s • ∑ a, boundedSiteMatrix (j.val + 1) site s a •
        ((v ⟨j,a⟩).val i : UnitAddCircle) := by
    change ((((∑ s : S, (T j e s : ℝ) • ∑ a : BoundedCoefficientExponent K (j.val + 1),
      (boundedSiteMatrix (j.val + 1) site s a : ℝ) • (v ⟨j,a⟩ : U j)) : U j).val i : ℝ) : UnitAddCircle) = _
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← zsmul_eq_mul, unitAddCircle_coe_sum, AddCircle.coe_zsmul]
  rw [AddCircle.coe_sub, he]
  exact add_sub_cancel _ _

variable [MeasurableSpace (CoefficientTorus (K := K) U)]
variable [BorelSpace (CoefficientTorus (K := K) U)]
variable (μ : Measure (CoefficientTorus (K := K) U)) [IsProbabilityMeasure μ]

noncomputable def coefficientSectionAmbientDensity
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (z : JetAmbientIndex (fun _ : Fin m => S) J → UnitAddCircle) : ℝ :=
  coefficientResidualAmbientDensity U R hR μ f (coefficientAmbientSiteSection T z)

theorem coefficientSectionAmbientDensity_lipschitz
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L A : ℝ≥0}
    (hf : LipschitzWith L f) {C : ℝ} (hfb : ∀ z, ‖f z‖ ≤ C)
    (hT : ∀ j e, ∑ s, ‖T j e s‖ ≤ A) :
    LipschitzWith (L * A) (coefficientSectionAmbientDensity U site q T μ f) :=
  (coefficientResidualAmbientDensity_lipschitz U R hR μ f hf hfb).comp
    (coefficientAmbientSiteSection_lipschitz T hT)

omit [∀ j, Fintype (J j)] [BorelSpace (CoefficientTorus (K := K) U)] in
theorem coefficientSectionAmbientDensity_bounds
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {C : ℝ}
    (hf : ∀ z, f z ∈ Set.Icc (0 : ℝ) C) (z) :
    coefficientSectionAmbientDensity U site q T μ f z ∈ Set.Icc (0 : ℝ) C :=
  coefficientResidualAmbientDensity_bounds U R hR μ f hf _

omit [∀ j, Fintype (J j)] [IsProbabilityMeasure μ] in
theorem coefficientSectionAmbientDensity_eq [μ.IsAddLeftInvariant]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ)
    (x : CoefficientTorus (K := K) U) :
    coefficientSectionAmbientDensity U site q T μ f
      (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x)) =
    linearQuotientAverage (coefficientIntegerLattice U) R hR μ
      (fun z => f (coefficientAmbientTorus U z))
      (quotientIntegerCover (coefficientIntegerLattice U) q x) := by
  let r := linearQuotientEndomorphism (coefficientIntegerLattice U) R hR
  have hadd (a b : CoefficientTorus (K := K) U) :
      coefficientAmbientTorus U (r (a + b)) =
        coefficientAmbientTorus U (r a) + coefficientAmbientTorus U (r b) := by
    funext t
    simp only [map_add, coefficientAmbientTorus, Pi.add_apply]
  have hinv (z : CoefficientAmbientIndex K J → UnitAddCircle) :
      coefficientResidualAmbientDensity U R hR μ f (z + coefficientAmbientTorus U (r x)) =
        coefficientResidualAmbientDensity U R hR μ f z := by
    have ht := integral_add_left_eq_self (μ := μ)
      (fun y => f (z + coefficientAmbientTorus U (r y))) x
    simpa only [coefficientResidualAmbientDensity, hadd, add_assoc] using ht
  rw [coefficientSectionAmbientDensity, ← hinv,
    coefficientAmbientSiteSection_residual U site q T x]
  exact coefficientResidualAmbientDensity_eq U R hR μ f _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_fixed_kernel_ambient_density_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℝ) {L C : ℝ≥0}
    (_hf : LipschitzWith L f) (_hcap : ∀ z, f z ∈ Set.Icc (0 : ℝ) C)
    (_hmass : (∫ x, f (coefficientAmbientTorus U x) ∂μ) = 1),
    let site := fun s k => affineSite root difference s (some k)
    let E := coefficientSiteTorusMap U site
    let π := Set.rangeFactorization E
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    ∃ (g : Set.range E → ℝ)
      (F : (JetAmbientIndex (fun _ : Fin m => Finset (Fin q)) J → UnitAddCircle) → ℝ),
      Continuous g ∧ (∀ y, g y ∈ Set.Icc (0 : ℝ) C) ∧
      Integrable g (μ.map π) ∧ (∫ y, g y ∂μ.map π) = 1 ∧
      (realDensityMeasure μ (fun x => f (coefficientAmbientTorus U (cover x)))).map π =
        realDensityMeasure (μ.map π) g ∧
      (∀ z, F z ∈ Set.Icc (0 : ℝ) C) ∧
      LipschitzWith (L * (Fintype.card (Finset (Fin q)) *
        Real.toNNReal (Real.exp ((P + A) ^ A)))) F ∧
      (∀ x, g (π x) = F (coefficientAmbientSiteEvaluation site (coefficientAmbientTorus U x))) ∧
      ∀ {X Index : Type*} [Fintype Index]
        (frequency : Index → ∀ j, (K →₀ ℕ) → J j → ℤ) (coeff : Index → ℂ) {η : ℝ},
        (∀ x, ‖coefficientTorusFourierSum U frequency coeff x - (f (coefficientAmbientTorus U x) : ℂ)‖ ≤ η) →
        ∀ (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
        (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j)) →
        ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j) (z : Option K → X → ℝ),
          ‖affineCubeFourierProjection U root difference frequency p coeff z -
            (g (π (affineCoefficientCoverSample U p hm d z)) : ℂ)‖ ≤ η := by
  obtain ⟨A, hA, hsection⟩ := exists_fixed_kernel_bounded_section_multiple m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hsection⟩ := hsection root₀ difference₀ a ha hperiod hP hK hsite period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro K _ root difference e hroot hdifference J _ U _ _ _ _ _ μ _ _ f L C hf hcap hmass site E π cover
  obtain ⟨T, hTb, hT⟩ := hsection root difference e hroot hdifference
  have hb (z) : ‖f z‖ ≤ C := by rw [Real.norm_of_nonneg (hcap z).1]; exact (hcap z).2
  obtain ⟨g, hgc, hgb, hgi, hgm, hg, hglaw⟩ :=
    exists_covered_coefficient_density U site d hd T (fun j x => hT j x) μ
      (fun x => f (coefficientAmbientTorus U x))
      (hf.continuous.comp (coefficientAmbientTorus_continuous U))
      (fun x => hcap _) hmass
  refine ⟨g, coefficientSectionAmbientDensity U site d T μ f,
    hgc, hgb, hgi, hgm, hglaw,
    coefficientSectionAmbientDensity_bounds U site d T μ f hcap, ?_, ?_, ?_⟩
  · apply coefficientSectionAmbientDensity_lipschitz U site d T μ f hf hb
    intro j i
    have hentry (s) : ‖T j i s‖ ≤ Real.exp ((P + A) ^ A) := by
      have h := (Finset.single_le_sum (fun k _ => abs_nonneg (T j k s : ℝ))
        (Finset.mem_univ i)).trans (hTb j s)
      simpa only [← Int.norm_cast_real, Real.norm_eq_abs] using h
    calc
      _ ≤ ∑ _s : Finset (Fin q), Real.exp ((P + A) ^ A) :=
        Finset.sum_le_sum (fun s _ => hentry s)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        NNReal.coe_mul, NNReal.coe_natCast, Real.toNNReal_of_nonneg (Real.exp_pos _).le]
                  rfl
  · intro x
    exact (hg x).trans (coefficientSectionAmbientDensity_eq U site d T μ f x).symm
  · intro X Index _ frequency coeff η happrox p hp hm z
    let R := coefficientSiteResidual U site (fun _ => d) T
    let hR := coefficientSiteResidual_preserves_lattice U site (fun _ => d) T
    have hfactor (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
        (coefficientArrayFunctional U frequency).comp R = 0 ↔
          affineCubeModeFactors U root difference frequency := by
      change (coefficientArrayFunctional U frequency).comp
        (coefficientSiteResidual U site (fun _ => d) T) = 0 ↔ _
      rw [coefficientSiteResidual_zero_iff U site (fun _ => d) T (fun _ => hd) (fun j x => hT j x),
        affineCubeModeFactors_iff_bounded]
    have he := coefficientTorusFourierProjection_approx_residualAverage U R hR root difference hfactor
      frequency coeff μ (fun x => f (coefficientAmbientTorus U x)) happrox
      (affineSampleCoefficientTorus U p hm z)
      (coefficientResidual_section_integrable U R hR μ _
        (hf.continuous.comp (coefficientAmbientTorus_continuous U)) (fun x => hb _) _)
    have hvalue := hg (affineCoefficientCoverSample U p hm d z)
    rw [affineCoefficientCoverSample_projection U p hm d hd z] at hvalue
    rw [hvalue]
    simpa only [coefficientTorusCharacter_sample U _ p hp hm z, affineCubeFourierProjection] using he

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedProjectedSpatialComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedSpatialLateLog (P Q : ℝ) : ℝ :=
  2 * Q + 3 + Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) * allocatedAmbientLog m P

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedSpatialLogPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedSpatialLateLog_nonneg {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ allocatedSpatialLateLog (G := G) B P Q := by
  have := allocatedAmbientLog_nonneg m hP
  unfold allocatedSpatialLateLog
  positivity

theorem exists_allocatedSpatialLateLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {P Q T : ℝ},
      0 ≤ P → 0 ≤ Q → P ≤ T → Q ≤ T →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ T →
      allocatedSpatialLateLog (G := G) B P Q ≤ (T + a) ^ a := by
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m + 1) * (4 * (Polynomial.X + 8)) + 8)
  let common : Polynomial ℕ := Polynomial.X + Polynomial.X * scalar + 1
  let width : Polynomial ℕ := Polynomial.C (m + 4) * (Polynomial.X + 8)
  let mixed : Polynomial ℕ := (2 * Polynomial.X + 1) * (width + common) + 3 * Polynomial.X + 1
  let ambient : Polynomial ℕ := Polynomial.X + Polynomial.X * (2 * mixed + 4 * Polynomial.X + 9) + 1
  let poly : Polynomial ℕ := 2 * Polynomial.X + 3 +
    Polynomial.C (m * (m + 1)) * (Polynomial.X + 1) ^ m * ambient
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ P Q T hP hQ hPT hQT hvars
  have hT : 0 ≤ T := hP.trans hPT
  have hslots : (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) ≤
      (m : ℝ) * (m + 1) * (T + 1) ^ m := by
    have h : (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) ≤
        (m : ℝ) * (m + 1) * ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) ^ m := by
      exact_mod_cast coefficientSlot_card_le (K := LayerSamplerVariables G I n B) m
    apply h.trans
    gcongr
  have hambient : allocatedAmbientLog m P ≤ allocatedAmbientLog m T := by
    dsimp only [allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog, allocatedCommonLog,
      allocatedScalarLog, integerInterpolationLogEnvelope]
    gcongr
  have hA0 := allocatedAmbientLog_nonneg m hP
  calc
    allocatedSpatialLateLog (G := G) B P Q ≤
        2 * T + 3 + ((m : ℝ) * (m + 1) * (T + 1) ^ m) * allocatedAmbientLog m T := by
      unfold allocatedSpatialLateLog
      gcongr
    _ ≤ _ := by
      simpa [poly, ambient, mixed, width, common, scalar, allocatedAmbientLog, allocatedMixedLog,
        allocatedWidthLog, allocatedCommonLog, allocatedScalarLog, integerInterpolationLogEnvelope,
        Polynomial.eval₂_pow] using hbound T hT

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleFullSliceLipschitz
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree short
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))
variable (lower width : ∀ a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis S.value a},
  B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)

noncomputable def allocatedOriginalSampleFullSliceMap (sample : Sample) (y : Input → ℝ) (o : Output) : ℝ :=
  MvPolynomial.eval (fun k => MvPolynomial.eval y
      (allocatedOriginalSampleSliceSubstitution B U basis S x u lower width k))
    (monomialArrayPolynomial Subtype.val (allocatedSampleNormalizedCoefficients B U basis S sample o.1.val)) /
      R o.1.val.1

noncomputable def allocatedOriginalSampleTailNoise (t : ℝ) (sample : Sample) : Coeff → ℝ :=
  activeTailRescale degree short (fun a => σ a.1 / t) (noise sample)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}

noncomputable def allocatedOriginalSampleFullSliceLip (t : ℝ) : ℝ≥0 :=
  (1 + Real.toNNReal |t|) * allocatedOriginalSampleLiftLip B U basis S

variable (x : G → IntegerScalarCubeBox Empty S.value)
variable (u : PrincipalAxisTuples (α := Empty)
  (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedFullMixedSiteValue
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : LayerSamplerAxis I n → ℝ
  | ⟨j, .inl i⟩ => (w j).1 i / R j
  | ⟨j, .inr i⟩ => ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

variable {α : Type*} [Fintype α] [DecidableEq α]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (r : ℝ≥0) (hr : 0 < r) (f : (LayerSamplerAxis I n → ℝ) → ℂ)

noncomputable def allocatedBufferedMixedSiteFactor
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : ℂ :=
  bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value) r hr f
    (allocatedFullMixedSiteValue (R := R) U b w)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

local notation "single" => (fun _ : Fin m => Unit)
local notation "ambient" => JetAmbientIndex single J

noncomputable def allocatedFullAmbientSiteCoordinates (z : ambient → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a =>
    let w := mixedRealCoordinates (euclideanSubspace (U a.1)) (b a.1) (o a.1)
      ((EuclideanSpace.equiv (J a.1) ℝ).symm (fun k => z ⟨a.1, (), k⟩))
    Sum.elim w.1 w.2 a.2 / R a.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "single" => (fun _ : Fin m => Unit)
local notation "quarter" => (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := Q) U o b d quarter

noncomputable def allocatedBufferedSiteChartFactor (f : (LayerSamplerAxis I n → ℝ) → ℂ) :
    EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun z =>
    allocatedBufferedMixedSiteFactor B U b S r hr f (fun j => mixedArrayRegroup _ _ _ (z.1 j) ()))

variable {α : Type*} [Fintype α] [DecidableEq α]


end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped NNReal

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

def singleSiteFromLayered (v : (Σ j, J j) → ℝ) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → ℝ := fun a => v ⟨a.1, a.2.2⟩

variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R : Fin m → ℝ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedTwistSpatialPartition
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenTorus
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (y : Y → UnitAddCircle) : ℂ :=
  W.mask residue * W.smooth (center, y)

theorem norm_frozenTorus_le
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (y : Y → UnitAddCircle) :
    ‖W.frozenTorus residue center y‖ ≤ 1 := by
  rw [frozenTorus, norm_mul]
  exact (mul_le_mul (W.mask_bound _) (W.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq
    (mul_one 1)

theorem frozenTorus_lipschitz
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    LipschitzWith L (W.frozenTorus residue center) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have h := W.smooth_lipschitz.dist_le_mul (center, y) (center, z)
  simp only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] at h
  calc
    _ = ‖W.mask residue‖ * dist (W.smooth (center, y)) (W.smooth (center, z)) := by
      simp only [frozenTorus, dist_eq_norm, ← mul_sub, norm_mul]
    _ ≤ 1 * ((L : ℝ) * dist y z) :=
      mul_le_mul (W.mask_bound _) h dist_nonneg zero_le_one
    _ = _ := one_mul _

theorem frozenTorus_spatial_error
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (x center : X → ℝ) (y : Y → UnitAddCircle) :
    ‖W.mask residue * W.smooth (x, y) - W.frozenTorus residue center y‖ ≤
      (L : ℝ) * dist x center := by
  have h := W.smooth_lipschitz.dist_le_mul (x, y) (center, y)
  simp only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] at h
  calc
    _ = ‖W.mask residue‖ * dist (W.smooth (x, y)) (W.smooth (center, y)) := by
      simp only [frozenTorus, dist_eq_norm, ← mul_sub, norm_mul]
    _ ≤ 1 * ((L : ℝ) * dist x center) :=
      mul_le_mul (W.mask_bound _) h dist_nonneg zero_le_one
    _ = _ := one_mul _

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) : ℂ :=
  W.frozenTorus (fun i => (u i : ZMod W.modulus)) center
    (physicalGridFactorInput W.cover p (fun i => (u i : ℝ)))

theorem eval_sub_frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (center : X → ℝ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    ‖W.eval N p u - W.frozenSpatialEval center p u‖ ≤
      (L : ℝ) * dist (fun i => (u i : ℝ) / N i) center :=
  W.frozenTorus_spatial_error _ _ _ _

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductIdealCutoff
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical Matrix

variable {α : Type*} [DecidableEq α]

namespace VectorPolynomial

variable {m : ℕ} {I J E : Fin m → Type*} {n : Fin m → ℕ}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable (rowSets : Fin m → Finset (Finset α))
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (d : ℕ)


end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r)

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedProductSiteCutoff (y : EuclideanJetLayers U rowTypes) : ℂ :=
  ∏ s : Finset α, allocatedBufferedSiteChartFactor B U b S o hb bW d r hr (fun _ => 1)
    (coveredRowsSiteValue rowSets U y s)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
variable (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
variable (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ))
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α]
variable (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedProductIdealSiteRadius : ℝ≥0 :=
  ⟨1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j,
    add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets j)))⟩

theorem allocatedProductIdealSiteRadius_one_le : 1 ≤ allocatedProductIdealSiteRadius (G := G) B rowSets := by
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets j)))

theorem allocatedProductIdealSiteRadius_dominates (j : Fin m) :
    (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤
      allocatedProductIdealSiteRadius (G := G) B rowSets := by
  change (rowSets j).card * allocatedIdealCoverSupport (G := G) B rowSets j ≤
    1 + ∑ k : Fin m, (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k
  exact (Finset.single_le_sum
    (f := fun k : Fin m => (rowSets k).card * allocatedIdealCoverSupport (G := G) B rowSets k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (allocatedIdealCoverSupport_nonneg B rowSets k))
    (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

variable [DecidableEq α]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedProductRadiusBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedProductGridRadius (C : Fin m → ℝ) (j : Fin m) : ℝ :=
  finiteRowChartRadius (((rowSets j).card + 1) * Fintype.card (Finset α))
    (Fintype.card (I j)) (C j) (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ))

theorem allocatedProductGridRadius_pos (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (j : Fin m) :
    0 < allocatedProductGridRadius (G := G) B rowSets C j :=
  finiteRowChartRadius_pos _ _ (hC j)
    (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)

theorem allocatedProductGridRadius_recovery_budget
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) (j : Fin m) :
    ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) *
        (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)))) ≤ 1 / 4 := by
  have h := finiteRowChartRadius_budget (((rowSets j).card + 1) * Fintype.card (Finset α))
    (Fintype.card (I j)) (hC j)
    (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg)
    (hR j) (hsmall j)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using h

theorem allocatedProductGridRadius_source_budget
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) {R : Fin m → ℝ} (hR : ∀ j, 0 ≤ R j)
    (hsmall : ∀ j, R j ≤ allocatedProductGridRadius (G := G) B rowSets C j) (j : Fin m) :
    C j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)) ≤ 1 / 4 := by
  have hcard : (1 : ℝ) ≤ Fintype.card (Finset α) := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨(∅ : Finset α)⟩)
  have hrow : (0 : ℝ) ≤ (rowSets j).card := Nat.cast_nonneg _
  have hfactor : (1 : ℝ) ≤ ((rowSets j).card + 1 : ℝ) * Fintype.card (Finset α) := by nlinarith
  have hc : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) *
      (2 * (allocatedProductIdealSiteRadius (G := G) B rowSets : ℝ) * R j)) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by norm_num) (allocatedProductIdealSiteRadius (G := G) B rowSets).coe_nonneg) (hR j)))
  have h := mul_le_mul_of_nonneg_right hfactor hc
  have hb := allocatedProductGridRadius_recovery_budget B rowSets C hC hR hsmall j
  simp only [one_mul, mul_assoc] at h hb ⊢
  exact h.trans hb

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalPeriodPrimitiveBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

theorem canonicalCoefficientDeckPeriodCap_le_exp {m : ℕ} (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] {period : ℕ} {L : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp L) :
    coefficientDeckPeriodCap O Q period ≤
      Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) := by
  unfold coefficientDeckPeriodCap
  calc
    _ ≤ ∏ j, ∏ _i : Q j, Real.exp ((Fintype.card (O j) : ℝ) * L) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j _
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
    _ = _ := by
      simp only [← Real.exp_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem periodFunctionLabelCard_le_exp {m : ℕ} (Q : Fin m → Type*)
    [∀ j, Fintype (Q j)] {period : ℕ} [NeZero period] {L : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp L) :
    (Fintype.card (∀ j, Q j → ZMod period) : ℝ) ≤
      Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * L) := by
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
    Nat.cast_prod, Nat.cast_pow]
  calc
    _ ≤ ∏ j, Real.exp ((Fintype.card (Q j) : ℝ) * L) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j _
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
    _ = _ := (Real.exp_sum _ _).symm

theorem canonicalPeriod_primitive_bounds {m M period : ℕ} [NeZero period]
    (A : Type*) [Fintype A] (n : Fin m → ℕ) (O Q : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (Q j)] {Pk : ℝ}
    (hM : (M : ℝ) ≤ Real.exp Pk) (hperiod : period ≤ M ^ (m + 1)) :
    let L := ((m + 1 : ℕ) : ℝ) * Pk
    let maskLog := (Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)
    let labelLog := (∑ j, (n j : ℝ) * L) + ∑ j, (Fintype.card (Q j) : ℝ) * L
    (period : ℝ) ≤ Real.exp L ∧
    (layerKernelIndexBound m M : ℝ) ^ Fintype.card A * coefficientDeckPeriodCap O Q period ≤
      Real.exp maskLog ∧
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤
      Real.exp labelLog := by
  intro L maskLog labelLog
  have hp : (period : ℝ) ≤ Real.exp L := by
    calc
      _ ≤ ((M ^ (m + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hperiod
      _ = (M : ℝ) ^ (m + 1) := Nat.cast_pow _ _
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hk : (layerKernelIndexBound m M : ℝ) ^ Fintype.card A ≤
      Real.exp ((Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hM) _
  have hd := canonicalCoefficientDeckPeriodCap_le_exp O Q hp
  have hleft := periodFunctionLabelCard_le_exp (fun j => Fin (n j)) hp
  have hright := periodFunctionLabelCard_le_exp Q hp
  refine ⟨hp, ?_, ?_⟩
  · calc
      _ ≤ Real.exp ((Fintype.card A : ℝ) * ((m * 2 ^ (m + 1) : ℕ) * Pk)) *
          Real.exp (∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (O j) * L)) :=
        mul_le_mul hk hd (coefficientDeckPeriodCap_nonneg O Q period) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  · have hh := mul_le_mul hleft hright (Nat.cast_nonneg
        (Fintype.card (∀ j, Q j → ZMod period))) (Real.exp_nonneg _)
    rw [Fintype.card_prod, Nat.cast_mul]
    simpa only [Nat.card_fin, ← Real.exp_add, labelLog,
      ← Nat.card_eq_fintype_card] using hh

end Erdos3.VectorPolynomial

end

end OAI

end


