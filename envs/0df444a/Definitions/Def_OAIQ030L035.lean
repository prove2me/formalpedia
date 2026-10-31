-- Prove2me | Definitions.Def_OAIQ030L035
-- name    : OAIQ030L035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:40:27.859019+00:00
-- url     : https://prove2.me/theorems/28c19c08-5804-450c-a4e9-781e0addff36
-- title:
--   Definitions bundle OAIQ030L035 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 137 declarations of OpenAI's Lean: 90 definitions, 1 inductive type or structure and 46 theorems. The definitions and types are `OAI.LaughlinGap.RealOccupation.FourCertificate`, `OAI.LaughlinGap.RealOccupation.RationalRow.fourMatrix`, `OAI.LaughlinGap.RealOccupation.RationalRow.fourSum`, `OAI.LaughlinGap.RealOccupation.RationalRow.threeSum`, `OAI.LaughlinGap.RealOccupation.RationalRow.threeTrace`, `OAI.LaughlinGap.RealOccupation.RationalRow.toReal`, `OAI.LaughlinGap.RealOccupation.auxiliaryFour`, `OAI.LaughlinGap.RealOccupation.auxiliaryThree`, `OAI.LaughlinGap.RealOccupation.copyDiagonal`, `OAI.LaughlinGap.RealOccupation.copyNormalization`, `OAI.LaughlinGap.RealOccupation.creation`, `OAI.LaughlinGap.RealOccupation.embeddingFamily`, `OAI.LaughlinGap.RealOccupation.fockLowering`, `OAI.LaughlinGap.RealOccupation.fourAnnihilator`, `OAI.LaughlinGap.RealOccupation.fourAverage`, `OAI.LaughlinGap.RealOccupation.fourColumn`, `OAI.LaughlinGap.RealOccupation.fourComparison`, `OAI.LaughlinGap.RealOccupation.fourComparisonStar`, `OAI.LaughlinGap.RealOccupation.fourHighestAverage`, `OAI.LaughlinGap.RealOccupation.fourHighestRowsStar`, `OAI.LaughlinGap.RealOccupation.fourLocalHighestStar`, `OAI.LaughlinGap.RealOccupation.fourRowScale`, `OAI.LaughlinGap.RealOccupation.fourTarget`, `OAI.LaughlinGap.RealOccupation.fourTermCoefficient`, `OAI.LaughlinGap.RealOccupation.fourTermEval`, `OAI.LaughlinGap.RealOccupation.localFourCoordinates`, `OAI.LaughlinGap.RealOccupation.physicalFour`, `OAI.LaughlinGap.RealOccupation.physicalHamiltonian`, `OAI.LaughlinGap.RealOccupation.physicalPair`, `OAI.LaughlinGap.RealOccupation.physicalPairPair`, `OAI.LaughlinGap.RealOccupation.physicalTriple`, `OAI.LaughlinGap.RealOccupation.rationalCreatedGram`, `OAI.LaughlinGap.RealOccupation.rationalFourComparison`, `OAI.LaughlinGap.RealOccupation.rationalFourCompression`, `OAI.LaughlinGap.RealOccupation.retainedFourTarget`, `OAI.LaughlinGap.RealOccupation.rootSetWeight`, `OAI.LaughlinGap.RealOccupation.rowAnnihilator`, `OAI.LaughlinGap.RealOccupation.rowEta`, `OAI.LaughlinGap.RealOccupation.rowFour`, `OAI.LaughlinGap.RealOccupation.rowFourMatrix` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinGap_AuxiliaryComparison`, `LaughlinGap_Contraction`, `LaughlinGap_CovariantFamily`, `LaughlinGap_ExactRows`, `LaughlinGap_FastCoupling`, `LaughlinGap_Four`, `LaughlinGap_FourAllowance`, `LaughlinGap_FourAveraging`, `LaughlinGap_FourBoundCore`, `LaughlinGap_FourComparison`, `LaughlinGap_FourTransfer`, `LaughlinGap_GlobalBoundCore`, `LaughlinGap_IntertwinerAveraging`, `LaughlinGap_IntertwiningSpin`, `LaughlinGap_LowNested`, `LaughlinGap_NestedAveraging`, `LaughlinGap_NestedSpin`, `LaughlinGap_PairDecomposition`, `LaughlinGap_PhysicalAveraging`, `LaughlinGap_RationalCreatedGram`, `LaughlinGap_RationalExterior`, `LaughlinGap_RationalFourCertificate`, `LaughlinGap_RationalFourCoefficients`, `LaughlinGap_RationalFourRows`, `LaughlinGap_RationalRows`, `LaughlinGap_RealOccupation`, `LaughlinGap_RealSpinSquare`, `LaughlinGap_SpectralBound`, `LaughlinGap_SpinAveraging`, `LaughlinGap_TensorSpin`, `LaughlinGap_ThreeAveraging`, `LaughlinGap_ThreeBounds`, `LaughlinGap_ThreeGram`, `LaughlinGap_ThreeSpin`.
--
--   **Imports.** It imports the bundles `OAIQ030L026`, `OAIQ030L027`, `OAIQ030L028`, `OAIQ030L029` and `OAIQ030L030` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.LaughlinGap.RealOccupation.Certificate10.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate11.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate12.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate13.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate14.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate15.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate16.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate17.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate18.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate19.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate20.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate21.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate22.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate23.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate7.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate9.certificate`, `OAI.LaughlinGap.RealOccupation.exact_four`, `OAI.LaughlinGap.RealOccupation.fourCertificate_of_tables`, `OAI.LaughlinGap.RealOccupation.four_comparison_of_certificates`, `OAI.LaughlinGap.RealOccupation.four_comparison_pointwise`, `OAI.LaughlinGap.RealOccupation.physical_spin_square_split` and `OAI.LaughlinGap.RealOccupation.three_comparison_of_strict_traces`; the proofs of `OAI.LaughlinGap.RealOccupation.Certificate10.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate11.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate12.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate13.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate14.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate15.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate16.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate17.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate18.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate19.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate20.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate21.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate22.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate23.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate7.certificate`, `OAI.LaughlinGap.RealOccupation.Certificate9.certificate`, `OAI.LaughlinGap.RealOccupation.exact_four`, `OAI.LaughlinGap.RealOccupation.fourCertificate_of_tables`, `OAI.LaughlinGap.RealOccupation.four_comparison_of_certificates`, `OAI.LaughlinGap.RealOccupation.four_comparison_pointwise`, `OAI.LaughlinGap.RealOccupation.physical_spin_square_split`, `OAI.LaughlinGap.RealOccupation.three_comparison_of_strict_traces` and `OAI.LaughlinGap.thm_main`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ030L026
import Definitions.Def_OAIQ030L027
import Definitions.Def_OAIQ030L028
import Definitions.Def_OAIQ030L029
import Definitions.Def_OAIQ030L030

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpectralBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators Topology
open Filter

noncomputable def threeBodyTailTerm (Q z : ℕ) : ℝ :=
  if 17 ≤ z ∧ Odd z ∧ z ≤ Q then
    threeBodyDimensionRatio Q z * |threeBodyGramCoefficient Q z| * ((z : ℝ) + 1)
  else 0

noncomputable def threeBodyTail (Q : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (Q + 1), threeBodyTailTerm Q z

end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Contraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators InnerProduct Topology

section BlockOperator
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

@[simp] lemma blockOperator_apply (M : Matrix ι ι ℂ) (T : E →L[ℂ] E)
    (x : ColumnSpace ι E) (b : ι) : blockOperator M T x b = ∑ c, M b c • T (x c) := by
  classical
  simp [blockOperator, columnInclusion_apply, smul_ite]

end BlockOperator
end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealOccupation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Occupation. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def creation {n : ℕ} (j : Fin n) : FockMatrix n :=
  (annihilation j).transpose

@[simp] theorem complexify_creation {n : ℕ} (j : Fin n) :
    complexify (creation j) = Occupation.creation j := by
  rw [creation, complexify_transpose, complexify_annihilation]
  exact Occupation.annihilation_adjoint j

noncomputable def secondQuantization {n : ℕ} (L : Matrix (Fin n) (Fin n) ℝ) : FockMatrix n :=
  ∑ i, ∑ j, L i j • (creation i * annihilation j)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_TensorSpin
attribute [-simp] _root_.OAI.LaughlinGap.Spin.highestCoefficient_zero_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

@[simp] lemma normalized_zero (S : LadderSystem ι) (x : ι → ℝ) (d : ℕ) :
    S.normalized x d 0 = x := by simp [normalized, normalizationFactor]

lemma normalized_succ (S : LadderSystem ι) (x : ι → ℝ) {d l : ℕ} (hl : l < d) :
    S.normalized x d (l+1) =
      (1 / Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l))) • S.lower (S.normalized x d l) := by
  have hα : 0 ≤ ((l : ℝ)+1)*((d : ℝ)-l) := by
    have hld : (l : ℝ) < d := by exact_mod_cast hl
    positivity
  simp only [normalized, raw_succ, normalizationFactor_succ hl.le,
    Real.sqrt_mul hα, map_smul, smul_smul, one_div_mul_one_div]

lemma normalized_weight (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (l : ℕ) :
    S.weight (S.normalized x d l) = ((d : ℝ)-2*l) • S.normalized x d l := by
  simp only [normalized, map_smul, S.weight_raw hw]
  exact smul_comm _ _ _

theorem normalized_norm_sq (S : LadderSystem ι) {x : ι → ℝ} {d l : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (hl : l ≤ d) :
    dotProduct (S.normalized x d l) (S.normalized x d l) = dotProduct x x := by
  have hf : 0 < normalizationFactor d l := normalizationFactor_pos hl
  have hs : Real.sqrt (normalizationFactor d l) ≠ 0 := (Real.sqrt_pos.mpr hf).ne'
  have heq := Real.sq_sqrt hf.le
  simp only [normalized, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    S.raw_norm_sq hw he (by omega : l ≤ d+1)]
  change (1 / Real.sqrt (normalizationFactor d l)) *
    ((1 / Real.sqrt (normalizationFactor d l)) *
      (normalizationFactor d l * dotProduct x x)) = dotProduct x x
  field_simp
  rw [heq]

end LadderSystem

namespace LadderSystem
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def onFirst (S : LadderSystem ι) : LadderSystem (ι × κ) where
  lower := onFirstEnd S.lower
  raise := onFirstEnd S.raise
  weight := onFirstEnd S.weight
  adjoint x y := by
    simp only [dotProduct, Fintype.sum_prod_type, onFirstEnd_apply]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun p q => x (p,q) * S.raise (fun i => y (i,q)) p)]
    apply Finset.sum_congr rfl
    intro q hq
    exact S.adjoint (fun p => x (p,q)) (fun p => y (p,q))
  raise_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.raise_lower (fun i => x (i,q))) p
  weight_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.weight_lower (fun i => x (i,q))) p

noncomputable def onSecond (S : LadderSystem κ) : LadderSystem (ι × κ) where
  lower := onSecondEnd S.lower
  raise := onSecondEnd S.raise
  weight := onSecondEnd S.weight
  adjoint x y := by
    simp only [dotProduct, Fintype.sum_prod_type, onSecondEnd_apply]
    apply Finset.sum_congr rfl
    intro p hp
    exact S.adjoint (fun q => x (p,q)) (fun q => y (p,q))
  raise_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.raise_lower (fun j => x (p,j))) q
  weight_lower x := by
    funext ⟨p,q⟩
    exact congrFun (S.weight_lower (fun j => x (p,j))) q

noncomputable def tensor (S : LadderSystem ι) (T : LadderSystem κ) :
    LadderSystem (ι × κ) where
  lower := onFirstEnd S.lower + onSecondEnd T.lower
  raise := onFirstEnd S.raise + onSecondEnd T.raise
  weight := onFirstEnd S.weight + onSecondEnd T.weight
  adjoint x y := by
    simp only [LinearMap.add_apply, add_dotProduct, dotProduct_add]
    exact congrArg₂ (· + ·) (S.onFirst.adjoint x y) (T.onSecond.adjoint x y)
  raise_lower x := by
    simp only [LinearMap.add_apply, map_add]
    rw [show onFirstEnd S.raise (onFirstEnd S.lower x) =
        onFirstEnd S.lower (onFirstEnd S.raise x) + onFirstEnd S.weight x from
          S.onFirst.raise_lower x,
      show onSecondEnd T.raise (onSecondEnd T.lower x) =
        onSecondEnd T.lower (onSecondEnd T.raise x) + onSecondEnd T.weight x from
          T.onSecond.raise_lower x,
      tensor_factor_commute S.raise T.lower x, ← tensor_factor_commute S.lower T.raise x]
    abel
  weight_lower x := by
    simp only [LinearMap.add_apply, map_add, smul_add]
    rw [show onFirstEnd S.weight (onFirstEnd S.lower x) =
        onFirstEnd S.lower (onFirstEnd S.weight x) - (2 : ℝ) • onFirstEnd S.lower x from
          S.onFirst.weight_lower x,
      show onSecondEnd T.weight (onSecondEnd T.lower x) =
        onSecondEnd T.lower (onSecondEnd T.weight x) - (2 : ℝ) • onSecondEnd T.lower x from
          T.onSecond.weight_lower x,
      tensor_factor_commute S.weight T.lower x, ← tensor_factor_commute S.lower T.weight x]
    abel

end LadderSystem

noncomputable def tensorSpin (n m : ℕ) : LadderSystem (Fin (n+1) × Fin (m+1)) :=
  (standardLadderSystem n).tensor (standardLadderSystem m)

lemma tensorSpin_weight (n m : ℕ) (x : (Fin (n+1) × Fin (m+1)) → ℝ)
    (p : Fin (n+1)) (q : Fin (m+1)) :
    (tensorSpin n m).weight x (p,q) = ((n : ℝ)+m-2*(p.val+q.val)) * x (p,q) := by
  simp only [tensorSpin, LadderSystem.tensor, standardLadderSystem,
    LinearMap.add_apply, onFirstEnd_apply, onSecondEnd_apply, Pi.add_apply, weight_apply]
  ring

lemma tensorSpin_lower (n m : ℕ) (x : (Fin (n+1) × Fin (m+1)) → ℝ)
    (p : Fin (n+1)) (q : Fin (m+1)) :
    (tensorSpin n m).lower x (p,q) =
      lowering n (fun i => x (i,q)) p + lowering m (fun j => x (p,j)) q := rfl

lemma tensorSpin_raise (n m : ℕ) (x : (Fin (n+1) × Fin (m+1)) → ℝ)
    (p : Fin (n+1)) (q : Fin (m+1)) :
    (tensorSpin n m).raise x (p,q) =
      raising n (fun i => x (i,q)) p + raising m (fun j => x (p,j)) q := rfl

theorem highestTensor_weight {n m z : ℕ} (hz : z ≤ min n m) :
    (tensorSpin n m).weight (highestTensor n m z) =
      ((n+m-2*z : ℕ) : ℝ) • highestTensor n m z := by
  have hzn : z ≤ n := (le_min_iff.mp hz).1
  have hzm : z ≤ m := (le_min_iff.mp hz).2
  have hzsum : 2*z ≤ n+m := by omega
  funext ⟨p,q⟩
  rw [tensorSpin_weight]
  simp only [highestTensor, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · have hc : (p.val : ℝ)+q.val = z := by exact_mod_cast h
    rw [hc, Nat.cast_sub hzsum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  · simp

theorem highestTensor_raise {n m z : ℕ} (hz : z ≤ min n m) :
    (tensorSpin n m).raise (highestTensor n m z) = 0 := by
  have hzn : z ≤ n := (le_min_iff.mp hz).1
  have hzm : z ≤ m := (le_min_iff.mp hz).2
  funext ⟨p,q⟩
  rw [tensorSpin_raise]
  by_cases h : p.val+q.val+1 = z
  · have hp : p.val < n := by omega
    have hq : q.val < m := by omega
    rw [raising_apply_of_lt _ p hp, raising_apply_of_lt _ q hq]
    simp only [highestTensor, show p.val+1+q.val = z by omega,
      show p.val+(q.val+1) = z by omega, ite_true, Pi.zero_apply]
    have hc : (p.val : ℝ)+q.val+1 = z := by exact_mod_cast h
    have he : Real.sqrt (((q.val : ℝ)+1)*((m : ℝ)-q.val)) =
        Real.sqrt (((z : ℝ)-p.val)*((m : ℝ)-z+p.val+1)) := by
      congr 1
      rw [← hc]
      ring
    rw [he]
    simpa only [mul_comm] using highestCoefficient_raising hz (by omega : p.val < z)
  · have h₁ : raising n (fun i => highestTensor n m z (i,q)) p = 0 := by
      by_cases hp : p.val < n
      · rw [raising_apply_of_lt _ p hp]
        simp [highestTensor, show ¬ (p.val+1+q.val = z) by omega]
      · exact raising_apply_of_not_lt _ p hp
    have h₂ : raising m (fun j => highestTensor n m z (p,j)) q = 0 := by
      by_cases hq : q.val < m
      · rw [raising_apply_of_lt _ q hq]
        simp [highestTensor, show ¬ (p.val+(q.val+1) = z) by omega]
      · exact raising_apply_of_not_lt _ q hq
    simp only [h₁, h₂, zero_add, Pi.zero_apply]

theorem coupledTensor_succ (n m z l : ℕ) :
    coupledTensor n m z (l+1) =
      (1 / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l))) •
        (tensorSpin n m).lower (coupledTensor n m z l) := by
  funext ⟨p,q⟩
  simp only [Pi.smul_apply, smul_eq_mul, tensorSpin_lower]
  by_cases h : p.val+q.val = z+(l+1)
  · rw [coupledTensor, ite_eq_left h, coupledCoefficient]
    cases p using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, ↓reduceIte, zero_add, lowering_zero]
      cases q using Fin.cases with
      | zero => simp only [Fin.val_zero] at h; omega
      | succ q =>
        have hs := secondLoweringCoefficient_succ (0 : Fin (n+1)) q h
        simp only [Fin.val_zero] at hs
        rw [lowering_succ, hs]
        simp only [coupledTensor, Fin.val_zero, Fin.val_castSucc, zero_add,
          show q.val = z+l by simp only [Fin.val_zero, Fin.val_succ] at h; omega, ite_true]
        ring
    | succ p =>
      simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ↓reduceIte, Nat.add_sub_cancel, lowering_succ]
      rw [show firstLoweringCoefficient n m z l (p.val+1) =
          ladderStep n p / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l)) from
        firstLoweringCoefficient_succ n m z l p]
      cases q using Fin.cases with
      | zero =>
        have hs := secondLoweringCoefficient_last (m := m)
          (by simpa using h : p.succ.val = z+(l+1))
        simp only [Fin.val_succ] at hs
        rw [hs, lowering_zero]
        simp only [zero_mul, add_zero, coupledTensor, Fin.val_castSucc, Fin.val_zero,
          add_zero, ite_eq_left (by simp only [Fin.val_succ, Fin.val_zero] at h; omega : p.val = z+l)]
        ring
      | succ q =>
        have hs := secondLoweringCoefficient_succ p.succ q h
        simp only [Fin.val_succ] at hs
        rw [lowering_succ, hs]
        have h₁ : p.val+(q.val+1) = z+l := by simp only [Fin.val_succ] at h; omega
        have h₂ : p.val+1+q.val = z+l := by simp only [Fin.val_succ] at h; omega
        simp only [coupledTensor, Fin.val_castSucc, Fin.val_succ, ite_eq_left h₁, ite_eq_left h₂]
        ring
  · rw [coupledTensor, ite_eq_right h]
    have h₁ : lowering n (fun i => coupledTensor n m z l (i,q)) p = 0 := by
      cases p using Fin.cases with
      | zero => rfl
      | succ p =>
        rw [lowering_succ]
        have hn : p.val+q.val ≠ z+l := by simp only [Fin.val_succ] at h; omega
        simp only [coupledTensor, Fin.val_castSucc, ite_eq_right hn, mul_zero]
    have h₂ : lowering m (fun j => coupledTensor n m z l (p,j)) q = 0 := by
      cases q using Fin.cases with
      | zero => rfl
      | succ q =>
        rw [lowering_succ]
        have hn : p.val+q.val ≠ z+l := by simp only [Fin.val_succ] at h; omega
        simp only [coupledTensor, Fin.val_castSucc, ite_eq_right hn, mul_zero]
    simp only [h₁, h₂, zero_add, mul_zero]

theorem coupledTensor_eq_normalized {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    coupledTensor n m z l = (tensorSpin n m).normalized (highestTensor n m z) (n+m-2*z) l := by
  have hzsum : 2*z ≤ n+m := by have := le_min_iff.mp hz; omega
  induction l with
  | zero => simp
  | succ l ih =>
    rw [coupledTensor_succ, ih (by omega), LadderSystem.normalized_succ _ _ (by omega)]
    simp only [Nat.cast_sub hzsum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem coupledTensor_norm_sq {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    dotProduct (coupledTensor n m z l) (coupledTensor n m z l) = 1 := by
  rw [coupledTensor_eq_normalized hz hl, LadderSystem.normalized_norm_sq _
    (highestTensor_weight hz) (highestTensor_raise hz) hl, highestTensor_norm_sq hz]

theorem coupledTensor_weight {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    (tensorSpin n m).weight (coupledTensor n m z l) =
      (((n+m-2*z : ℕ) : ℝ)-2*l) • coupledTensor n m z l := by
  rw [coupledTensor_eq_normalized hz hl]
  exact LadderSystem.normalized_weight _ (highestTensor_weight hz) l

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

lemma raise_adjoint (S : LadderSystem ι) (x y : ι → ℝ) :
    dotProduct (S.raise x) y = dotProduct x (S.lower y) := by
  rw [dotProduct_comm, ← S.adjoint, dotProduct_comm]

lemma weight_eq (S : LadderSystem ι) (x : ι → ℝ) :
    S.weight x = S.raise (S.lower x) - S.lower (S.raise x) := by
  rw [S.raise_lower]
  abel

lemma weight_adjoint (S : LadderSystem ι) (x y : ι → ℝ) :
    dotProduct (S.weight x) y = dotProduct x (S.weight y) := by
  rw [S.weight_eq x, S.weight_eq y, sub_dotProduct, dotProduct_sub]
  simp only [S.raise_adjoint, S.adjoint]

noncomputable def casimir (S : LadderSystem ι) : Module.End ℝ (ι → ℝ) :=
  S.weight.comp S.weight + (2 : ℝ) • S.weight + (4 : ℝ) • S.lower.comp S.raise

lemma casimir_apply (S : LadderSystem ι) (x : ι → ℝ) :
    S.casimir x = S.weight (S.weight x) + (2 : ℝ) • S.weight x +
      (4 : ℝ) • S.lower (S.raise x) := rfl

lemma casimir_adjoint (S : LadderSystem ι) (x y : ι → ℝ) :
    dotProduct (S.casimir x) y = dotProduct x (S.casimir y) := by
  simp only [casimir_apply, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, S.weight_adjoint, S.adjoint, S.raise_adjoint]

lemma lower_raise_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hw : S.weight x = μ • x) (he : S.raise x = 0) (l : ℕ) :
    S.lower (S.raise (S.raw x l)) = ((l : ℝ)*(μ-l+1)) • S.raw x l := by
  cases l with
  | zero => simp [he]
  | succ l =>
    rw [S.raise_raw hw he, map_smul, raw_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    ring

lemma casimir_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hw : S.weight x = μ • x) (he : S.raise x = 0) (l : ℕ) :
    S.casimir (S.raw x l) = (μ*(μ+2)) • S.raw x l := by
  simp only [casimir_apply, S.lower_raise_raw hw he,
    map_smul, S.weight_raw hw, smul_smul, ← add_smul]
  congr 1
  ring

lemma casimir_normalized (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (l : ℕ) :
    S.casimir (S.normalized x d l) = ((d : ℝ)*(d+2)) • S.normalized x d l := by
  simp only [normalized, map_smul, S.casimir_raw hw he]
  exact smul_comm _ _ _

end LadderSystem

theorem coupledTensor_casimir {n m z l : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) :
    (tensorSpin n m).casimir (coupledTensor n m z l) =
      (((n+m-2*z : ℕ) : ℝ)*((n+m-2*z : ℕ)+2)) • coupledTensor n m z l := by
  rw [coupledTensor_eq_normalized hz hl]
  exact LadderSystem.casimir_normalized _ (highestTensor_weight hz) (highestTensor_raise hz) l

theorem coupledTensor_orthogonal_same_spin {n m z l k : ℕ} (hz : z ≤ min n m)
    (hl : l ≤ n+m-2*z) (hk : k ≤ n+m-2*z) (hlk : l ≠ k) :
    dotProduct (coupledTensor n m z l) (coupledTensor n m z k) = 0 := by
  apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).weight_adjoint
    (coupledTensor_weight hz hl) (coupledTensor_weight hz hk)
  intro h
  apply hlk
  have H : (l : ℝ) = k := by linarith
  exact_mod_cast H

theorem coupledTensor_orthogonal_distinct_spin {n m z w l k : ℕ}
    (hz : z ≤ min n m) (hw : w ≤ min n m)
    (hl : l ≤ n+m-2*z) (hk : k ≤ n+m-2*w) (hzw : z ≠ w) :
    dotProduct (coupledTensor n m z l) (coupledTensor n m w k) = 0 := by
  apply dot_eq_zero_of_distinct_eigenvalues _ (tensorSpin n m).casimir_adjoint
    (coupledTensor_casimir hz hl) (coupledTensor_casimir hw hk)
  have hd : n+m-2*z ≠ n+m-2*w := by
    have := le_min_iff.mp hz
    have := le_min_iff.mp hw
    omega
  have hd' : ((n+m-2*z : ℕ) : ℝ) ≠ (n+m-2*w : ℕ) := by exact_mod_cast hd
  have hsum : 0 < ((n+m-2*z : ℕ) : ℝ)+(n+m-2*w : ℕ)+2 := by positivity
  intro he
  have hh : (((n+m-2*z : ℕ) : ℝ)-(n+m-2*w : ℕ)) *
      (((n+m-2*z : ℕ) : ℝ)+(n+m-2*w : ℕ)+2) = 0 := by nlinarith
  exact hd' (sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hsum.ne'))

theorem coupledFamily_orthonormal (n m : ℕ) : Orthonormal ℝ (coupledFamily n m) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨z,l⟩ ⟨w,k⟩
  simp only [coupledFamily, EuclideanSpace.inner_toLp_toLp, star_trivial]
  rw [dotProduct_comm]
  have hz : z.val ≤ min n m := by omega
  have hw : w.val ≤ min n m := by omega
  have hl : l.val ≤ n+m-2*z.val := by omega
  have hk : k.val ≤ n+m-2*w.val := by omega
  by_cases hzw : z = w
  · subst w
    by_cases hlk : l = k
    · subst k
      rw [ite_eq_left rfl]
      exact coupledTensor_norm_sq hz hl
    · rw [ite_eq_right (by simpa using hlk : (Sigma.mk z l : CoupledIndex n m) ≠ ⟨z,k⟩)]
      exact coupledTensor_orthogonal_same_spin hz hl hk (fun h => hlk (Fin.ext h))
  · rw [ite_eq_right (fun h => hzw (congrArg Sigma.fst h))]
    exact coupledTensor_orthogonal_distinct_spin hz hw hl hk (fun h => hzw (Fin.ext h))

noncomputable def coupledBasis (n m : ℕ) :
    OrthonormalBasis (CoupledIndex n m) ℝ (EuclideanSpace ℝ (Fin (n+1) × Fin (m+1))) := by
  letI : Nonempty (CoupledIndex n m) := ⟨⟨0,0⟩⟩
  have hc : Fintype.card (CoupledIndex n m) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1) × Fin (m+1))) := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    exact coupledIndex_card n m
  let b := basisOfOrthonormalOfCardEqFinrank (coupledFamily_orthonormal n m) hc
  exact b.toOrthonormalBasis (by simpa [b] using coupledFamily_orthonormal n m)

@[simp] theorem coupledBasis_apply (n m : ℕ) (i : CoupledIndex n m) :
    coupledBasis n m i = coupledFamily n m i := by
  simp [coupledBasis]

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

lemma raw_top_succ (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) : S.raw x (d+1) = 0 := by
  apply dotProduct_self_eq_zero.mp
  rw [S.raw_norm_sq hw he (by omega)]
  simp

lemma normalized_lower (S : LadderSystem ι) (x : ι → ℝ) {d l : ℕ} (hl : l < d) :
    S.lower (S.normalized x d l) =
      Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l)) • S.normalized x d (l+1) := by
  have hα : 0 < ((l : ℝ)+1)*((d : ℝ)-l) := by
    have hld : (l : ℝ) < d := by exact_mod_cast hl
    exact mul_pos (by positivity) (by linarith)
  rw [normalized_succ _ _ hl, smul_smul, mul_one_div_cancel (Real.sqrt_pos.mpr hα).ne', one_smul]

lemma normalized_lower_top (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) :
    S.lower (S.normalized x d d) = 0 := by
  rw [normalized, map_smul, ← raw_succ, S.raw_top_succ hw he, smul_zero]

lemma normalized_raise_zero (S : LadderSystem ι) {x : ι → ℝ} (he : S.raise x = 0) (d : ℕ) :
    S.raise (S.normalized x d 0) = 0 := by simp [he]

lemma normalized_raise_succ (S : LadderSystem ι) {x : ι → ℝ} {d l : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (hl : l < d) :
    S.raise (S.normalized x d (l+1)) =
      Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l)) • S.normalized x d l := by
  have hα : 0 < ((l : ℝ)+1)*((d : ℝ)-l) := by
    have hld : (l : ℝ) < d := by exact_mod_cast hl
    exact mul_pos (by positivity) (by linarith)
  have ha : Real.sqrt (((l : ℝ)+1)*((d : ℝ)-l)) ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  have hf : Real.sqrt (normalizationFactor d l) ≠ 0 :=
    (Real.sqrt_pos.mpr (normalizationFactor_pos hl.le)).ne'
  simp only [normalized, map_smul, S.raise_raw hw he, smul_smul,
    normalizationFactor_succ hl.le, Real.sqrt_mul hα.le]
  congr 1
  field_simp
  rw [Real.sq_sqrt hα.le]

noncomputable def embedding (S : LadderSystem ι) (x : ι → ℝ) (d : ℕ) :
    (Fin (d+1) → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun a := ∑ l : Fin (d+1), a l • S.normalized x d l.val
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' t a := by simp [Finset.smul_sum, smul_smul]

lemma embedding_apply (S : LadderSystem ι) (x : ι → ℝ) (d : ℕ) (a : Fin (d+1) → ℝ) :
    S.embedding x d a = ∑ l : Fin (d+1), a l • S.normalized x d l.val := rfl

theorem embedding_lower (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (a : Fin (d+1) → ℝ) :
    S.lower (S.embedding x d a) = S.embedding x d (lowering d a) := by
  rw [embedding_apply, embedding_apply, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [map_smul, Fin.val_last, S.normalized_lower_top hw he,
    lowering_zero, zero_smul, smul_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [S.normalized_lower _ l.isLt, lowering_succ]
  simp only [ladderStep, smul_smul]
  congr 1
  ring

theorem embedding_raise (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (a : Fin (d+1) → ℝ) :
    S.raise (S.embedding x d a) = S.embedding x d (raising d a) := by
  rw [embedding_apply, embedding_apply, map_sum, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [map_smul, Fin.val_zero, S.normalized_raise_zero he,
    raising_last, zero_smul, smul_zero, add_zero, zero_add]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Fin.val_castSucc, Fin.val_succ]
  rw [S.normalized_raise_succ hw he l.isLt, raising_castSucc]
  simp only [ladderStep, smul_smul]
  congr 1
  ring

end LadderSystem

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwiningSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwining Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

structure LadderMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : LadderSystem ι) (T : LadderSystem κ) extends (ι → ℝ) →ₗ[ℝ] (κ → ℝ) where
  lower : ∀ x, T.lower (toLinearMap x) = toLinearMap (S.lower x)
  raise : ∀ x, T.raise (toLinearMap x) = toLinearMap (S.raise x)

namespace LadderMap
variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
variable {S : LadderSystem ι} {T : LadderSystem κ} {U : LadderSystem σ}

noncomputable def comp (B : LadderMap T U) (A : LadderMap S T) : LadderMap S U where
  toLinearMap := B.toLinearMap.comp A.toLinearMap
  lower x := by simp only [LinearMap.comp_apply, B.lower, A.lower]
  raise x := by simp only [LinearMap.comp_apply, B.raise, A.raise]

noncomputable def transpose (A : LadderMap S T) : LadderMap T S where
  toLinearMap := transposeMap A.toLinearMap
  lower x := by
    apply eq_of_dotProduct_eq
    intro a
    rw [← S.raise_adjoint, ← transposeMap_adjoint, ← A.raise,
      T.raise_adjoint, transposeMap_adjoint]
  raise x := by
    apply eq_of_dotProduct_eq
    intro a
    rw [← S.adjoint, ← transposeMap_adjoint, ← A.lower,
      T.adjoint, transposeMap_adjoint]

end LadderMap

noncomputable def LadderSystem.embeddingMap {ι : Type*} [Fintype ι]
    (S : LadderSystem ι) {x : ι → ℝ} {d : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) :
    LadderMap (standardLadderSystem d) S where
  toLinearMap := S.embedding x d
  lower a := S.embedding_lower hw he a
  raise a := S.embedding_raise hw he a

noncomputable def coupledEmbedding {n m z : ℕ} (hz : z ≤ min n m) :
    LadderMap (standardLadderSystem (n+m-2*z)) (tensorSpin n m) :=
  (tensorSpin n m).embeddingMap (highestTensor_weight hz) (highestTensor_raise hz)

lemma coupledEmbedding_apply {n m z : ℕ} (hz : z ≤ min n m)
    (a : Fin (n+m-2*z+1) → ℝ) :
    (coupledEmbedding hz).toLinearMap a =
      ∑ l : Fin (n+m-2*z+1), a l • coupledTensor n m z l.val := by
  simp only [coupledEmbedding, LadderSystem.embeddingMap, LadderSystem.embedding_apply,
    coupledTensor_eq_normalized hz (Nat.le_of_lt_succ (Fin.isLt _))]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

noncomputable def loweringMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) : Matrix ι ι ℝ := LinearMap.toMatrix' S.lower

lemma loweringMatrix_transpose {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) : (loweringMatrix S).transpose = LinearMap.toMatrix' S.raise := by
  ext i j
  have he := S.adjoint (Pi.single i 1) (Pi.single j 1)
  simpa [loweringMatrix, LinearMap.toMatrix'_apply, dotProduct_single, single_dotProduct] using he

noncomputable def commutantLadderMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : LadderSystem ι) {A : Matrix ι ι ℝ}
    (hA : A ∈ rotationCommutant (loweringMatrix S)) : LadderMap S S where
  toLinearMap := Matrix.toLin' A
  lower x := by
    have he := (rotationCommutant_mem _ _).mp hA |>.1
    have hh : loweringMatrix S * A = A * loweringMatrix S := sub_eq_zero.mp he
    have hr := congrArg (fun M : Matrix ι ι ℝ => Matrix.toLin' M x) hh
    simpa [loweringMatrix, Matrix.toLin'_mul] using hr
  raise x := by
    have he := (rotationCommutant_mem _ _).mp hA |>.2
    have hh : (loweringMatrix S).transpose * A = A * (loweringMatrix S).transpose :=
      sub_eq_zero.mp he
    rw [loweringMatrix_transpose] at hh
    have hr := congrArg (fun M : Matrix ι ι ℝ => Matrix.toLin' M x) hh
    simpa [Matrix.toLin'_mul] using hr

noncomputable def tensorProjection {n m z : ℕ} (hz : z ≤ min n m) :
    Matrix (Fin (n+1) × Fin (m+1)) (Fin (n+1) × Fin (m+1)) ℝ :=
  LinearMap.toMatrix' ((coupledEmbedding hz).comp (coupledEmbedding hz).transpose).toLinearMap

lemma coupledTensor_dot {n m : ℕ} (i j : CoupledIndex n m) :
    dotProduct (coupledTensor n m i.1.val i.2.val) (coupledTensor n m j.1.val j.2.val) =
      if i=j then 1 else 0 := by
  have hh := (orthonormal_iff_ite.mp (coupledFamily_orthonormal n m)) j i
  simpa only [coupledFamily, EuclideanSpace.inner_toLp_toLp, star_trivial, eq_comm] using hh

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CovariantFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Covariant Family. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

noncomputable def embeddingFamily {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (B : κ → Matrix σ σ ℝ) : ι → Matrix σ σ ℝ :=
  fun i => combination B (A.toLinearMap (Pi.single i 1))

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def LadderMap.tensorRight {ι κ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (U : LadderSystem σ) : LadderMap (S.tensor U) (T.tensor U) where
  toLinearMap := onFirstMap A.toLinearMap
  lower x := by
    change onFirstEnd T.lower (onFirstMap A.toLinearMap x) +
      onSecondEnd U.lower (onFirstMap A.toLinearMap x) =
      onFirstMap A.toLinearMap (onFirstEnd S.lower x + onSecondEnd U.lower x)
    rw [map_add, ← onFirstMap_onSecond]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.lower (fun i => x (i,q))) p
  raise x := by
    change onFirstEnd T.raise (onFirstMap A.toLinearMap x) +
      onSecondEnd U.raise (onFirstMap A.toLinearMap x) =
      onFirstMap A.toLinearMap (onFirstEnd S.raise x + onSecondEnd U.raise x)
    rw [map_add, ← onFirstMap_onSecond]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.raise (fun i => x (i,q))) p

noncomputable def tripleSpin (Q : ℕ) :=
  (tensorSpin Q Q).tensor (standardLadderSystem Q)

noncomputable def swap23 (Q : ℕ) : LadderMap (tripleSpin Q) (tripleSpin Q) where
  toLinearMap := swap23Linear Q
  lower x := by
    funext ⟨⟨i,j⟩,k⟩
    change lowering Q (fun i => x ((i,k),j)) i +
      lowering Q (fun j => x ((i,k),j)) j + lowering Q (fun k => x ((i,k),j)) k =
      lowering Q (fun i => x ((i,k),j)) i +
        lowering Q (fun k => x ((i,k),j)) k + lowering Q (fun j => x ((i,k),j)) j
    ring
  raise x := by
    funext ⟨⟨i,j⟩,k⟩
    change raising Q (fun i => x ((i,k),j)) i +
      raising Q (fun j => x ((i,k),j)) j + raising Q (fun k => x ((i,k),j)) k =
      raising Q (fun i => x ((i,k),j)) i +
        raising Q (fun k => x ((i,k),j)) k + raising Q (fun j => x ((i,k),j)) j
    ring

noncomputable def pairInclusion {Q : ℕ} (hQ : 2 ≤ Q) :
    LadderMap (standardLadderSystem (2*Q-2)) (tensorSpin Q Q) :=
  (tensorSpin Q Q).embeddingMap
    (show (tensorSpin Q Q).weight (highestTensor Q Q 1) =
        ((2*Q-2 : ℕ) : ℝ) • highestTensor Q Q 1 by
      have h := highestTensor_weight (n := Q) (m := Q) (z := 1) (by omega : 1 ≤ min Q Q)
      simpa only [mul_one, ← two_mul] using h)
    (highestTensor_raise (by omega : 1 ≤ min Q Q))

noncomputable def pairSpectatorInclusion {Q : ℕ} (hQ : 2 ≤ Q) :
    LadderMap (tensorSpin (2*Q-2) Q) (tripleSpin Q) :=
  (pairInclusion hQ).tensorRight (standardLadderSystem Q)

noncomputable def compressedSwap {Q : ℕ} (hQ : 2 ≤ Q) :
    LadderMap (tensorSpin (2*Q-2) Q) (tensorSpin (2*Q-2) Q) :=
  (pairSpectatorInclusion hQ).transpose.comp ((swap23 Q).comp (pairSpectatorInclusion hQ))

noncomputable def swapScalar (Q z : ℕ) (hQ : 2 ≤ Q) : ℝ :=
  dotProduct (highestTensor (2*Q-2) Q z)
    ((compressedSwap hQ).toLinearMap (highestTensor (2*Q-2) Q z))

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PhysicalAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin

noncomputable def fockLowering (Q : ℕ) : FockMatrix (Q+1) :=
  secondQuantization (loweringMatrix (standardLadderSystem Q))

noncomputable def physicalPair (Q p : ℕ) : FockMatrix (Q+1) :=
  (1/Real.sqrt 2) • combination (productFamily annihilation annihilation) (physicalPairTensor Q p)

noncomputable def physicalHamiltonian (Q : ℕ) : FockMatrix (Q+1) :=
  ∑ p : Fin (2*Q-1), (physicalPair Q p.val).transpose * physicalPair Q p.val

noncomputable def physicalTriple (Q : ℕ) :
    (Fin (2*Q-2+1) × Fin (Q+1)) → FockMatrix (Q+1) :=
  productFamily (fun p => physicalPair Q p.val) annihilation

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_PairDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pair Decomposition. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct ComplexOrder
open Occupation

noncomputable def tensorSwap (Q : ℕ) : LadderMap (tensorSpin Q Q) (tensorSpin Q Q) where
  toLinearMap := {
    toFun := fun x ij => x (ij.2,ij.1)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  lower x := by
    funext ⟨i,j⟩
    change lowering Q (fun i => x (j,i)) i + lowering Q (fun j => x (j,i)) j =
      lowering Q (fun j => x (j,i)) j + lowering Q (fun i => x (j,i)) i
    ring
  raise x := by
    funext ⟨i,j⟩
    change raising Q (fun i => x (j,i)) i + raising Q (fun j => x (j,i)) j =
      raising Q (fun j => x (j,i)) j + raising Q (fun i => x (j,i)) i
    ring

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntertwinerAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intertwiner Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators
open Averaging

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def LadderMap.matrix {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) : Matrix κ ι ℝ := LinearMap.toMatrix' A.toLinearMap

omit [DecidableEq κ] in
@[simp] lemma LadderMap.matrix_mulVec {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (x : ι → ℝ) : A.matrix.mulVec x = A.toLinearMap x :=
  LinearMap.toMatrix'_mulVec A.toLinearMap x

noncomputable def copyLift {S : LadderSystem ι} {T : LadderSystem κ}
    (A B : LadderMap S T) : Matrix ι ι ℝ →ₗ[ℝ] Matrix κ κ ℝ where
  toFun X := A.matrix * X * B.matrix.transpose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp [Matrix.mul_smul, Matrix.smul_mul]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedSpin
attribute [-simp] _root_.OAI.LaughlinGap.Spin.LadderMap.matrix_mulVec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

noncomputable def LadderMap.tensorLeft {ι κ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype σ]
    {S : LadderSystem ι} {T : LadderSystem κ}
    (A : LadderMap S T) (U : LadderSystem σ) : LadderMap (U.tensor S) (U.tensor T) where
  toLinearMap := onSecondMap A.toLinearMap
  lower x := by
    change onFirstEnd U.lower (onSecondMap A.toLinearMap x) +
      onSecondEnd T.lower (onSecondMap A.toLinearMap x) =
      onSecondMap A.toLinearMap (onFirstEnd U.lower x + onSecondEnd S.lower x)
    rw [map_add, ← onSecondMap_onFirst]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.lower (fun i => x (p,i))) q
  raise x := by
    change onFirstEnd U.raise (onSecondMap A.toLinearMap x) +
      onSecondEnd T.raise (onSecondMap A.toLinearMap x) =
      onSecondMap A.toLinearMap (onFirstEnd U.raise x + onSecondEnd S.raise x)
    rw [map_add, ← onSecondMap_onFirst]
    congr 1
    funext ⟨p,q⟩
    exact congrFun (A.raise (fun i => x (p,i))) q

noncomputable def nestedSpin (n m k : ℕ) :=
  (standardLadderSystem n).tensor (tensorSpin m k)

noncomputable def nestedEmbedding {n m k r z : ℕ} (hr : r ≤ min m k)
    (hz : z ≤ min n (m+k-2*r)) :
    LadderMap (standardLadderSystem (n+(m+k-2*r)-2*z)) (nestedSpin n m k) :=
  ((coupledEmbedding hr).tensorLeft (standardLadderSystem n)).comp (coupledEmbedding hz)

abbrev NestedIndex (n m k : ℕ) :=
  (r : Fin (min m k+1)) × CoupledIndex n (m+k-2*r.val)

noncomputable def nestedFamily (n m k : ℕ) (a : NestedIndex n m k) :
    EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1))) :=
  WithLp.toLp 2 (nestedTensor n m k a.1.val a.2.1.val a.2.2.val)

lemma coupled_tensor_second_dot {n m k r s : ℕ} (hr : r ≤ min m k) (hs : s ≤ min m k)
    (x : (Fin (n+1) × Fin (m+k-2*r+1)) → ℝ)
    (y : (Fin (n+1) × Fin (m+k-2*s+1)) → ℝ) :
    dotProduct (onSecondMap (coupledEmbedding hr).toLinearMap x)
      (onSecondMap (coupledEmbedding hs).toLinearMap y) =
      ∑ p : Fin (n+1), ∑ l : Fin (m+k-2*r+1), ∑ t : Fin (m+k-2*s+1),
        x (p,l) * y (p,t) * if r=s ∧ l.val=t.val then (1:ℝ) else 0 := by
  rw [dotProduct, Fintype.sum_prod_type]
  simp only [onSecondMap_apply, coupledEmbedding_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have hd := coupledTensor_dot (⟨⟨r,by omega⟩,l⟩ : CoupledIndex m k) ⟨⟨s,by omega⟩,t⟩
  have he : ((⟨⟨r,by omega⟩,l⟩ : CoupledIndex m k) = ⟨⟨s,by omega⟩,t⟩) ↔
      r=s ∧ l.val=t.val := by
    constructor
    · intro h
      exact ⟨congrArg (fun a : CoupledIndex m k => a.1.val) h,
        congrArg (fun a : CoupledIndex m k => a.2.val) h⟩
    · rintro ⟨rfl,hl⟩
      have : l=t := Fin.ext hl
      subst t
      rfl
  rw [if_congr he rfl rfl] at hd
  rw [← hd, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma nestedTensor_as_map {n m k r z l : ℕ} (hr : r ≤ min m k) :
    nestedTensor n m k r z l = onSecondMap (coupledEmbedding hr).toLinearMap
      (coupledTensor n (m+k-2*r) z l) := by
  funext a
  simp [nestedTensor, onSecondMap, coupledEmbedding_apply]

lemma nestedTensor_dot (n m k : ℕ) (a b : NestedIndex n m k) :
    dotProduct (nestedTensor n m k a.1.val a.2.1.val a.2.2.val)
      (nestedTensor n m k b.1.val b.2.1.val b.2.2.val) = if a=b then 1 else 0 := by
  rcases a with ⟨r,a⟩
  rcases b with ⟨s,b⟩
  rw [nestedTensor_as_map (Nat.le_of_lt_succ r.isLt),
    nestedTensor_as_map (Nat.le_of_lt_succ s.isLt), coupled_tensor_second_dot]
  by_cases he : r=s
  · subst s
    simp only [true_and, Fin.val_inj, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    convert coupledTensor_dot a b using 1
    all_goals try with_reducible_and_instances rfl
    simp only [dotProduct, Fintype.sum_prod_type]
  · have hv : r.val ≠ s.val := by exact fun hv => he (Fin.ext hv)
    have hab : (⟨r,a⟩ : NestedIndex n m k) ≠ ⟨s,b⟩ := by
      intro h; exact he (congrArg Sigma.fst h)
    simp [hv,hab]

lemma nestedFamily_orthonormal (n m k : ℕ) : Orthonormal ℝ (nestedFamily n m k) := by
  rw [orthonormal_iff_ite]
  intro a b
  simpa only [nestedFamily, EuclideanSpace.inner_toLp_toLp, star_trivial, eq_comm] using
    nestedTensor_dot n m k b a

lemma nestedIndex_card (n m k : ℕ) :
    Fintype.card (NestedIndex n m k) = (n+1)*((m+1)*(k+1)) := by
  change Fintype.card ((r : Fin (min m k+1)) × CoupledIndex n (m+k-2*r.val)) = _
  rw [Fintype.card_sigma]
  simp only [coupledIndex_card]
  rw [← Finset.mul_sum]
  have hh := coupledIndex_card m k
  change Fintype.card ((z : Fin (min m k+1)) × Fin (m+k-2*z.val+1)) = _ at hh
  rw [Fintype.card_sigma] at hh
  simp only [Fintype.card_fin] at hh
  rw [hh]

noncomputable def nestedBasis (n m k : ℕ) : OrthonormalBasis (NestedIndex n m k) ℝ
    (EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1)))) := by
  letI : Nonempty (NestedIndex n m k) := ⟨⟨0,0,0⟩⟩
  have hc : Fintype.card (NestedIndex n m k) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1) × (Fin (m+1) × Fin (k+1)))) := by
    rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, nestedIndex_card]
  let b := basisOfOrthonormalOfCardEqFinrank (nestedFamily_orthonormal n m k) hc
  exact b.toOrthonormalBasis (by simpa [b] using nestedFamily_orthonormal n m k)

@[simp] lemma nestedBasis_apply (n m k : ℕ) (a : NestedIndex n m k) :
    nestedBasis n m k a = nestedFamily n m k a := by simp [nestedBasis]

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def LadderMap.changeSource {n d : ℕ} {S : LadderSystem ι} (h : n=d)
    (A : LadderMap (standardLadderSystem n) S) : LadderMap (standardLadderSystem d) S :=
  h ▸ A

noncomputable def nestedAtDeficit {n m k D r : ℕ} (hr : r ≤ min m k) (hrD : r ≤ D)
    (hz : D-r ≤ min n (m+k-2*r)) :
    LadderMap (standardLadderSystem (n+m+k-2*D)) (nestedSpin n m k) :=
  (nestedEmbedding hr hz).changeSource (by omega)

end LaughlinGap.Spin

namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Averaging Spin
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def physicalFour (Q : ℕ) :
    (Fin (2*Q-2+1) × (Fin (Q+1) × Fin (Q+1))) → FockMatrix (Q+1) :=
  fun a => (1/Real.sqrt 2) •
    productFamily (fun p => physicalPair Q p.val) (productFamily annihilation annihilation) a

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_LowNested
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low Nested. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def lowNestedInclusion {Q T : ℕ} (hQ : 2 ≤ Q) (hT : T ≤ Q)
    (a : LowNestedIndex T) : NestedIndex (2*Q-2) Q Q :=
  ⟨⟨a.2.val, by have := a.1.isLt; have := a.2.isLt; omega⟩,
    ⟨⟨a.1.val-a.2.val, (lowNested_valid hQ hT (by have := a.1.isLt; omega)
      (by have := a.2.isLt; exact Nat.le_of_lt_succ this)).2.1 |> Nat.lt_succ_of_le⟩,
    ⟨T-a.1.val, (lowNested_valid hQ hT (by have := a.1.isLt; omega)
      (by have := a.2.isLt; exact Nat.le_of_lt_succ this)).2.2 |> Nat.lt_succ_of_le⟩⟩⟩

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Averaging. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

noncomputable def fourAnnihilator (Q D T r : ℕ) : FockMatrix (Q+1) :=
  combination (physicalFour Q) (nestedTensor (2*Q-2) Q Q r (D-r) (T-D))

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Bounds. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def threeSpinLift {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) : FockMatrix (Q+1) :=
  lift (physicalTriple Q) (tensorProjection (show z ≤ min (2*Q-2) Q by omega))

noncomputable def threeTailLift {Q : ℕ} (hQ : 2 ≤ Q) : FockMatrix (Q+1) :=
  ∑ z : Fin (Q+1), if 16 ≤ z.val then
    (threeBodyGramCoefficient Q z.val) • threeSpinLift hQ (Nat.le_of_lt_succ z.isLt) else 0

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Averaging. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def lowCoupledInclusion {n m T : ℕ} (hT : T ≤ min n m)
    (z : Fin (T+1)) : CoupledIndex n m :=
  ⟨⟨z.val, by omega⟩, ⟨T-z.val, by dsimp; have := z.isLt; omega⟩⟩

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_AuxiliaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Auxiliary Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

noncomputable def rowTriple {Q : ℕ} (hQ : 8 ≤ Q) (a : Fin 8 × Fin 9) :
    FockMatrix (Q+1) :=
  annihilation ⟨a.2.val,by omega⟩ * physicalPair Q a.1.val

noncomputable def rowAnnihilator {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) : FockMatrix (Q+1) :=
  r.lam • physicalPair Q r.t.val + ∑ a : RowEntry r.t,
    r.alpha a • (creation ⟨a.output.val,by have := a.output.isLt; omega⟩ * rowTriple hQ a.val)

noncomputable def rowThree {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) : FockMatrix (Q+1) :=
  (∑ a : RowEntry r.t, (r.lam*r.alpha a) •
    ((rowTriple hQ (r.t,a.output)).transpose * rowTriple hQ a.val +
      (rowTriple hQ a.val).transpose * rowTriple hQ (r.t,a.output))) +
  ∑ a : RowEntry r.t, ∑ b : RowEntry r.t, (r.alpha a*r.alpha b) •
    (if a.output=b.output then (rowTriple hQ a.val).transpose * rowTriple hQ b.val else 0)

noncomputable def rowFour {Q : ℕ} (hQ : 8 ≤ Q) (r : RowData) : FockMatrix (Q+1) :=
  -(∑ a : RowEntry r.t, ∑ b : RowEntry r.t, (r.alpha a*r.alpha b) •
    ((annihilation ⟨b.output.val,by have := b.output.isLt; omega⟩ * rowTriple hQ a.val).transpose *
      (annihilation ⟨a.output.val,by have := a.output.isLt; omega⟩ * rowTriple hQ b.val)))

noncomputable def threeHighestAverage (Q z : ℕ) : FockMatrix (Q+1) :=
  average (rotationCommutant (fockLowering Q))
    ((combination (physicalTriple Q) (highestTensor (2*Q-2) Q z)).transpose *
      combination (physicalTriple Q) (highestTensor (2*Q-2) Q z))

noncomputable def rowTrace (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ) (r : RowData) : ℝ :=
  (∑ a : RowEntry r.t, 2*r.lam*r.alpha a *
    s z (r.t.val+a.output.val) r.t.val *
    s z (r.t.val+a.output.val) a.val.1.val) +
  ∑ a : RowEntry r.t, ∑ b : RowEntry r.t,
    if a.output=b.output then r.alpha a*r.alpha b *
      s z (r.t.val+a.output.val) a.val.1.val *
      s z (r.t.val+a.output.val) b.val.1.val else 0

noncomputable def rowThreeTrace (Q z : ℕ) (r : RowData) : ℝ :=
  rowTrace (threeWeightCoefficient Q) z r

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Gram. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

noncomputable def orderedThreeWedge {Q : ℕ} (hQ : 2 ≤ Q) :
    ((Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) →ₗ[ℝ]
      (ThreeIndex (Fin (Q+1)) → ℝ) :=
  (Real.sqrt 3)⁻¹ • ((cyclicSum (Fin (Q+1))).comp (pairSpectatorInclusion hQ).toLinearMap)

noncomputable def orderedThreeGram {Q : ℕ} (hQ : 2 ≤ Q) :
    Module.End ℝ ((Fin (2*Q-2+1) × Fin (Q+1)) → ℝ) :=
  (transposeMap (orderedThreeWedge hQ)).comp (orderedThreeWedge hQ)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RealSpinSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Spin Square. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Occupation

noncomputable def fourTarget (Q : ℕ) : FockMatrix (Q+1) :=
  ∑ p : Fin (2*Q-1), ∑ q : Fin (2*Q-1),
    (physicalPair Q q.val * physicalPair Q p.val).transpose *
      (physicalPair Q q.val * physicalPair Q p.val)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_GlobalBoundCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology
variable {ι : Type*} [Fintype ι]

noncomputable def rowEta (rows : ι → RowData) : ℝ := ∑ r, (rows r).lam^2

noncomputable def auxiliaryThree {Q : ℕ} (hQ : 8 ≤ Q) (rows : ι → RowData) : FockMatrix (Q+1) :=
  ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (∑ r, rowThree hQ (rows r))
noncomputable def auxiliaryFour {Q : ℕ} (hQ : 8 ≤ Q) (rows : ι → RowData) : FockMatrix (Q+1) :=
  ((2*Q-1:ℕ):ℝ) • average (rotationCommutant (fockLowering Q)) (∑ r, rowFour hQ (rows r))

noncomputable def threeRetained {Q : ℕ} (hQ : 15 ≤ Q) : FockMatrix (Q+1) :=
  ∑ z : Fin 16, threeBodyGramCoefficient Q z.val •
    threeSpinLift (by omega : 2 ≤ Q) (show z.val ≤ Q by omega)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

noncomputable def rowNormalization (t p j : ℕ) : ℝ :=
  (Real.sqrt 2)^p * rootFactorial t * rootFactorial (p+j-t) /
    ((Real.sqrt 2)^t * rootFactorial p * rootFactorial j)

noncomputable def RationalRow.toReal (r : RationalRow) : RowData where
  t := r.t
  lam := r.lam
  alpha a := (r.alpha a.val.1 a.val.2 : ℝ) * rowNormalization r.t.val a.val.1.val a.val.2.val

noncomputable def threeRowScale (t z i : ℕ) : ℝ :=
  if z ≤ t+i then (Real.sqrt 2)^z * rootFactorial t * rootFactorial i /
    ((Real.sqrt 3)^(t+i)*(Real.sqrt 2)^t*rootFactorial z*rootFactorial (t+i-z)) else 0

def RationalRow.threeSum (r : RationalRow) (z : ℕ) (i : Fin 9) : ℚ :=
  ∑ a : RowEntry r.t, if a.output=i then
    r.alpha a.val.1 a.val.2 * uCoefficient 2 z (r.t.val+i.val) a.val.1.val else 0

def RationalRow.threeTrace (r : RationalRow) (z : ℕ) : ℚ :=
  ∑ i : Fin 9, threeRowFactor r.t.val z i.val * r.threeSum z i *
    (r.threeSum z i + 2*r.lam*uCoefficient 2 z (r.t.val+i.val) r.t.val)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ExactRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def traceRational (z : ℕ) : ℚ :=
  ∑ a : Fin 8, ∑ i : Fin 9, threeRowFactor a.val z i.val *
    (exactRows a).threeSumFast z i *
      ((exactRows a).threeSumFast z i + 2*(exactRows a).lam*uCoefficient 2 z (a.val+i.val) a.val)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourAllowance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Allowance. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

noncomputable def localFourCoordinates {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q)
    (b : OrbitalTriple D) : FockMatrix (Q+1) :=
  let a := orbitalTripleFinite hQ hD b
  annihilation a.2.val.2 * annihilation a.2.val.1 * physicalPair Q a.1.val

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def fourHighestAverage (Q D r s : ℕ) : FockMatrix (Q+1) :=
  average (rotationCommutant (fockLowering Q))
    ((fourAnnihilator Q D D r).transpose * fourAnnihilator Q D D s)

noncomputable def rowFourMatrix
    (s : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) (D : ℕ) (r : RowData) :
    Matrix (FourCopy D) (FourCopy D) ℝ := fun u v =>
  -(∑ a : RowEntry r.t, ∑ b : RowEntry r.t, r.alpha a*r.alpha b *
    s D (a.val.1.val+a.val.2.val+b.output.val) u.val.val a.val.1.val a.val.2.val b.output.val *
    s D (a.val.1.val+a.val.2.val+b.output.val) v.val.val b.val.1.val b.val.2.val a.output.val)

noncomputable def fourAverage (Q D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℝ →ₗ[ℝ] FockMatrix (Q+1) :=
  (average (rotationCommutant (fockLowering Q))).comp
    (lift (fun r : FourCopy D => fourAnnihilator Q D D r.val.val))

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Transfer. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

variable {ι : Type*} [Fintype ι]

noncomputable def fourComparison (rows : ι → RowData) (ε : ℝ) (Q D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℝ :=
  fourDimensionRatio Q D • fourCopyTarget D -
    ∑ a, rowFourMatrix (fourWeightCoefficient Q) D (rows a) + ε • 1

noncomputable def fourComparisonStar (rows : ι → RowData) (ε : ℝ) (D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℝ :=
  (2:ℝ) • fourCopyTarget D -
    ∑ a, rowFourMatrix fourWeightCoefficientStar D (rows a) + ε • 1

noncomputable def fourHighestRowsStar (D : ℕ) :
    Matrix (FourCopy D) (OrbitalTriple D) ℝ := fun r b =>
  fourBodyCoefficientStar D D r.val.val b.val.1 b.val.2.1 b.val.2.2

noncomputable def fourLocalHighestStar {D : ℕ} (hD : D ≤ 23)
    (r : FourCopy D) : Module.End ℂ (Occupation.Hilbert 25) :=
  ∑ b : OrbitalTriple D, (fourHighestRowsStar D r b : ℂ) •
    (Occupation.annihilation (localTripleK hD b) * Occupation.annihilation (localTripleJ hD b) *
      Occupation.localPairStar 25 (localTripleP hD b).val)

def FourCertificate (rows : ι → RowData) (ε : ℝ) (D : ℕ) (hD : D ≤ 23) : Prop :=
  (Occupation.createdGram (fourLocalHighestStar hD) *
    (fourComparisonStar rows ε D).map (algebraMap ℝ ℂ) *
      Occupation.createdGram (fourLocalHighestStar hD)).PosSemidef

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Coefficients. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

noncomputable def copyNormalization (D r : ℕ) : ℝ :=
  1/(rootFactorial r*rootFactorial (D-r))

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Exterior. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def fourTermCoefficient (D r : ℕ) (a : FourTerm D) : ℚ :=
  vCoefficient D D r (fourTermP a) (fourTermJ a) (fourTermK a) * (2:ℚ)^((r+1)/2) *
    ((fourTermX a:ℚ)-(fourTermY a:ℚ)) * (fourTermP a).factorial *
      (fourTermJ a).factorial * (fourTermK a).factorial / (2:ℚ)^D

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalCreatedGram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Created Gram. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators InnerProduct
open Spin

noncomputable def rootSetWeight {n : ℕ} (A : Finset (Fin n)) : ℝ :=
  ∏ a ∈ A, rootFactorial a.val

def fourColumn {D : ℕ} (hD : D ≤ 23) (r : ℕ) (A : Finset (Fin 25)) : ℚ :=
  ∑ a : FourTerm D, if (fourTermLabels hD a).toFinset=A then
    fourTermCoefficient D r a * Occupation.wordSign (fourTermLabels hD a) else 0

def rationalCreatedGram {D : ℕ} (hD : D ≤ 23) : Matrix (FourCopy D) (FourCopy D) ℚ :=
  fun u v => ∑ A ∈ fourKeys hD, fourColumn hD u.val.val A * fourColumn hD v.val.val A / setFactorial A

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

noncomputable def fourRowScale (t D i k : ℕ) : ℝ :=
  if D ≤ t+i+k then rootFactorial t * rootFactorial i * rootFactorial k /
    ((2:ℝ)^(t+i+k)*Real.sqrt 2^t*rootFactorial (t+i+k-D)) else 0

def RationalRow.fourSum (r : RationalRow) (D s : ℕ) (i k : Fin 9) : ℚ :=
  ∑ a : RowEntry r.t, if a.output=i then r.alpha a.val.1 a.val.2 *
    vCoefficient D (r.t.val+i.val+k.val) s a.val.1.val a.val.2.val k.val *
      (2:ℚ)^((s+1)/2+a.val.1.val) else 0

def RationalRow.fourMatrix (r : RationalRow) (D : ℕ) : Matrix (FourCopy D) (FourCopy D) ℚ :=
  fun u v => -(∑ i : Fin 9, ∑ k : Fin 9, fourRowFactor r.t.val D i.val k.val *
    r.fourSum D u.val.val i k * r.fourSum D v.val.val k i)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Coupling. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def fourTermEval (D r : ℕ) (a : FourTerm D) : ℚ :=
  vFast D D r (fourTermP a) (fourTermJ a) (fourTermK a) * (2:ℚ)^((r+1)/2) *
    ((fourTermX a:ℚ)-(fourTermY a:ℚ)) * (fourTermP a).factorial *
      (fourTermJ a).factorial * (fourTermK a).factorial / (2:ℚ)^D

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Four
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def physicalPairPair (Q : ℕ) :
    (Fin (2*Q-2+1) × Fin (2*Q-2+1)) → FockMatrix (Q+1) :=
  productFamily (fun p => physicalPair Q p.val) (fun p => physicalPair Q p.val)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourBoundCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Bound Core. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def retainedFourTarget (Q : ℕ) : FockMatrix (Q+1) :=
  ∑ d : Fin 23, ((4*Q-1-2*(d.val+1):ℕ):ℝ) • fourHighestAverage Q (d.val+1) 1 1

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Certificate. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

def rationalFourComparison (rows : ι → RationalRow) (ε : ℚ) (D : ℕ) :
    Matrix (FourCopy D) (FourCopy D) ℚ := fun u v =>
  (if u=v then ((if u.val.val=1 then 2 else 0)+ε)*copyNormalizationSq D u.val.val else 0) -
    copyNormalizationSq D u.val.val * (∑ a, (rows a).fourMatrix D u v) *
      copyNormalizationSq D v.val.val

def rationalFourCompression (rows : ι → RationalRow) (ε : ℚ) {D : ℕ} (hD : D ≤ 23) :
    Matrix (FourCopy D) (FourCopy D) ℚ :=
  rationalCreatedGram hD * rationalFourComparison rows ε D * rationalCreatedGram hD

noncomputable def copyDiagonal (D : ℕ) : Matrix (FourCopy D) (FourCopy D) ℂ :=
  Matrix.diagonal (fun r => (copyNormalization D r.val.val:ℂ))

end LaughlinGap.RealOccupation

end

end OAI
end


