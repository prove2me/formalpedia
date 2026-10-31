-- Prove2me | Definitions.Def_OAIQ030L028
-- name    : OAIQ030L028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T02:37:34.149303+00:00
-- url     : https://prove2.me/theorems/54e92ecb-fa40-408f-ab7c-01a2acfe0dfc
-- title:
--   Definitions bundle OAIQ030L028 of the split of OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.LaughlinGap.thm_main`, carved from OpenAI's openai/math development (OpenAI, *Uniform Laughlin gap and stability under bounded scalar disorder (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 57 definitions, 1 instance and 41 theorems. The definitions and types are `OAI.LaughlinGap.RealOccupation.Certificate18.fibers`, `OAI.LaughlinGap.RealOccupation.Certificate22.representatives`, `OAI.LaughlinGap.RealOccupation.SumTable10.sums`, `OAI.LaughlinGap.RealOccupation.SumTable11.sums`, `OAI.LaughlinGap.RealOccupation.SumTable12.sums`, `OAI.LaughlinGap.RealOccupation.SumTable13.sums`, `OAI.LaughlinGap.RealOccupation.SumTable14.sums`, `OAI.LaughlinGap.RealOccupation.SumTable16.sums`, `OAI.LaughlinGap.RealOccupation.SumTable18.sums`, `OAI.LaughlinGap.RealOccupation.SumTable21.sums`, `OAI.LaughlinGap.RealOccupation.SumTable22.sums`, `OAI.LaughlinGap.RealOccupation.SumTable5.sums`, `OAI.LaughlinGap.RealOccupation.SumTable7.sums`, `OAI.LaughlinGap.RealOccupation.SumTable8.sums`, `OAI.LaughlinGap.RealOccupation.SumTable9.sums`, `OAI.LaughlinGap.RealOccupation.checkFourFibersSound`, `OAI.LaughlinGap.RealOccupation.checkFourTerms`, `OAI.LaughlinGap.RealOccupation.etaRational`, `OAI.LaughlinGap.RealOccupation.exactFourEval`, `OAI.LaughlinGap.RealOccupation.exactFourInteger`, `OAI.LaughlinGap.RealOccupation.exactRows`, `OAI.LaughlinGap.RealOccupation.fourCopyEquiv`, `OAI.LaughlinGap.RealOccupation.fourKeys`, `OAI.LaughlinGap.RealOccupation.fourSumInteger`, `OAI.LaughlinGap.RealOccupation.fourTermJ`, `OAI.LaughlinGap.RealOccupation.fourTermK`, `OAI.LaughlinGap.RealOccupation.fourTermLabels`, `OAI.LaughlinGap.RealOccupation.fourTermP`, `OAI.LaughlinGap.RealOccupation.fourTermX`, `OAI.LaughlinGap.RealOccupation.fourTermY`, `OAI.LaughlinGap.RealOccupation.fourWeightCoefficient`, `OAI.LaughlinGap.RealOccupation.integerTableEval`, `OAI.LaughlinGap.RealOccupation.tableComparison`, `OAI.LaughlinGap.RealOccupation.threeWeightCoefficient`, `OAI.LaughlinGap.RealOccupation.threeWeightCoefficientStar`, `OAI.LaughlinGap.RealOccupation.vInt`, `OAI.LaughlinGap.Spin.FourCoordinates`, `OAI.LaughlinGap.Spin.coupledFamily`, `OAI.LaughlinGap.Spin.cycleIndex`, `OAI.LaughlinGap.Spin.cycleMap` and 17 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `LaughlinGap_AuxiliaryComparison`, `LaughlinGap_CachedIntegerRows`, `LaughlinGap_Certificate18`, `LaughlinGap_Certificate22`, `LaughlinGap_Contraction`, `LaughlinGap_ExactRows`, `LaughlinGap_FastFourKeys`, `LaughlinGap_FourAllowance`, `LaughlinGap_FourAveraging`, `LaughlinGap_FourComparison`, `LaughlinGap_FourSpin`, `LaughlinGap_FourTables`, `LaughlinGap_IntegerFourRows`, `LaughlinGap_NestedSpin`, `LaughlinGap_PairDecomposition`, `LaughlinGap_RationalCreatedGram`, `LaughlinGap_RationalExterior`, `LaughlinGap_RationalFourComputable`, `LaughlinGap_SpectralBound`, `LaughlinGap_SpinWork`, `LaughlinGap_SumTable10`, `LaughlinGap_SumTable11`, `LaughlinGap_SumTable12`, `LaughlinGap_SumTable13`, `LaughlinGap_SumTable14`, `LaughlinGap_SumTable16`, `LaughlinGap_SumTable18`, `LaughlinGap_SumTable21`, `LaughlinGap_SumTable22`, `LaughlinGap_SumTable5`, `LaughlinGap_SumTable7`, `LaughlinGap_SumTable8`, `LaughlinGap_SumTable9`, `LaughlinGap_TensorSpin`, `LaughlinGap_ThreeComparison`, `LaughlinGap_ThreeGram`, `LaughlinGap_ThreeSpectrum`, `LaughlinGap_ThreeSpin`, `LaughlinGap_WedgeIdentification`.
--
--   **Imports.** It imports the bundles `OAIQ030L000`, `OAIQ030L002`, `OAIQ030L004`, `OAIQ030L008`, `OAIQ030L009`, `OAIQ030L010`, `OAIQ030L011`, `OAIQ030L012`, `OAIQ030L014`, `OAIQ030L015`, `OAIQ030L016`, `OAIQ030L017`, `OAIQ030L018`, `OAIQ030L019`, `OAIQ030L020`, `OAIQ030L021`, `OAIQ030L022`, `OAIQ030L023`, `OAIQ030L024` and `OAIQ030L025` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ030L035`; the statements `OAI.LaughlinGap.RealOccupation.Certificate15.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate16.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate17.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate18.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate19.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate20.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate21.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate22.fibers_checked`, `OAI.LaughlinGap.RealOccupation.Certificate22.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate23.fibers_checked`, `OAI.LaughlinGap.RealOccupation.Certificate23.keys_checked` and `OAI.LaughlinGap.RealOccupation.Certificate23.rows_checked`; the proofs of `OAI.LaughlinGap.RealOccupation.Certificate15.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate16.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate17.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate18.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate19.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate20.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate21.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate22.fibers_checked`, `OAI.LaughlinGap.RealOccupation.Certificate22.rows_checked`, `OAI.LaughlinGap.RealOccupation.Certificate23.fibers_checked`, `OAI.LaughlinGap.RealOccupation.Certificate23.keys_checked` and `OAI.LaughlinGap.RealOccupation.Certificate23.rows_checked`.
-- source:
--   OpenAI, Uniform Laughlin gap and stability under bounded scalar disorder (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ030L000
import Definitions.Def_OAIQ030L002
import Definitions.Def_OAIQ030L004
import Definitions.Def_OAIQ030L008
import Definitions.Def_OAIQ030L009
import Definitions.Def_OAIQ030L010
import Definitions.Def_OAIQ030L011
import Definitions.Def_OAIQ030L012
import Definitions.Def_OAIQ030L014
import Definitions.Def_OAIQ030L015
import Definitions.Def_OAIQ030L016
import Definitions.Def_OAIQ030L017
import Definitions.Def_OAIQ030L018
import Definitions.Def_OAIQ030L019
import Definitions.Def_OAIQ030L020
import Definitions.Def_OAIQ030L021
import Definitions.Def_OAIQ030L022
import Definitions.Def_OAIQ030L023
import Definitions.Def_OAIQ030L024
import Definitions.Def_OAIQ030L025

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

noncomputable def threeBodyGramCoefficient (Q z : ℕ) : ℝ :=
  (-1 : ℝ) ^ z * fallingRatio Q z *
    (3 * (z : ℝ) - 1 - (z : ℝ) * ((z : ℝ) + 1) / (Q : ℝ))

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

noncomputable def columnInclusion (b : ι) : E →L[ℂ] ColumnSpace ι E :=
  (((WithLp.linearEquiv 2 ℂ (ι → E)).symm.toLinearMap).comp
    (LinearMap.single ℂ (fun _ : ι => E) b)).toContinuousLinearMap

@[simp] lemma columnInclusion_apply (b c : ι) (x : E) :
    columnInclusion b x c = if c = b then x else 0 := by
  change (Pi.single b x : ι → E) c = _
  rw [Pi.single_apply]

noncomputable def blockOperator (M : Matrix ι ι ℂ) (T : E →L[ℂ] E) :
    ColumnSpace ι E →L[ℂ] ColumnSpace ι E :=
  ∑ b, ∑ c, M b c • (columnInclusion b).comp (T.comp (columnProjection c))

end BlockOperator
end LaughlinGap

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SpinWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spin Work. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators Topology
open Filter

lemma highestFactor_pos {n m z k : ℕ} (hz : z ≤ min n m) (hk : k < z) :
    0 < highestFactor n m z k := by
  have hzN : (z : ℝ) ≤ n := by exact_mod_cast (le_min_iff.mp hz).1
  have hzM : (z : ℝ) ≤ m := by exact_mod_cast (le_min_iff.mp hz).2
  have hkZ : (k : ℝ) < z := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  exact div_pos (by linarith) (by linarith)

lemma highestWeight_nonneg {n m z p : ℕ} (hz : z ≤ min n m) :
    0 ≤ highestWeight n m z p := by
  by_cases hp : p ≤ z
  · apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg fun k hk =>
      (highestFactor_pos hz ((Finset.mem_range.mp hk).trans_le hp)).le
  · simp [highestWeight, Nat.choose_eq_zero_of_lt (by omega : z < p)]

@[simp] lemma highestWeight_zero (n m z : ℕ) : highestWeight n m z 0 = 1 := by
  simp [highestWeight]

lemma highestNormalization_pos {n m z : ℕ} (hz : z ≤ min n m) :
    0 < highestNormalization n m z := by
  apply Finset.sum_pos' (fun p _ => highestWeight_nonneg hz)
  exact ⟨0, by simp, by simp⟩

lemma highestCoefficient_sq {n m z p : ℕ} (hz : z ≤ min n m) :
    highestCoefficient n m z p ^ 2 =
      highestWeight n m z p / highestNormalization n m z := by
  simp only [highestCoefficient, div_pow, mul_pow, ← pow_mul (-1 : ℝ),
    mul_comm (z-p) 2, pow_mul (-1 : ℝ) 2, neg_one_sq, one_pow, one_mul,
    Real.sq_sqrt (highestWeight_nonneg hz), Real.sq_sqrt (highestNormalization_pos hz).le]

theorem highestCoefficient_sum_sq {n m z : ℕ} (hz : z ≤ min n m) :
    ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 = 1 := by
  simp_rw [highestCoefficient_sq hz]
  rw [← Finset.sum_div]
  exact div_self (highestNormalization_pos hz).ne'

lemma highestCoefficient_eq_zero {n m z p : ℕ} (hp : z < p) :
    highestCoefficient n m z p = 0 := by
  simp [highestCoefficient, highestWeight, Nat.choose_eq_zero_of_lt hp]

lemma highestWeight_step {n m z p : ℕ} (hz : z ≤ min n m) (hp : p < z) :
    highestWeight n m z (p+1) * ((p : ℝ)+1) * ((n : ℝ)-p) =
      highestWeight n m z p * ((z : ℝ)-p) * ((m : ℝ)-z+p+1) := by
  have hnp : (n : ℝ) - p ≠ 0 := by
    have hn : p < n := hp.trans_le (le_min_iff.mp hz).1
    exact sub_ne_zero.mpr (Ne.symm (by exact_mod_cast hn.ne))
  have hc : (z.choose (p+1) : ℝ) * ((p : ℝ)+1) = (z.choose p : ℝ) * ((z : ℝ)-p) := by
    have H := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_succ_right_eq z p)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp.le] using H
  simp only [highestWeight, Finset.prod_range_succ, highestFactor]
  rw [mul_assoc (z.choose (p+1) : ℝ), mul_comm _ ((p : ℝ)+1),
    ← mul_assoc (z.choose (p+1) : ℝ), hc]
  field_simp

theorem highestCoefficient_raising {n m z p : ℕ} (hz : z ≤ min n m) (hp : p < z) :
    highestCoefficient n m z (p+1) * Real.sqrt (((p : ℝ)+1)*((n : ℝ)-p)) +
      highestCoefficient n m z p * Real.sqrt (((z : ℝ)-p)*((m : ℝ)-z+p+1)) = 0 := by
  have he : Real.sqrt (highestWeight n m z (p+1)) *
      Real.sqrt (((p : ℝ)+1)*((n : ℝ)-p)) =
      Real.sqrt (highestWeight n m z p) *
      Real.sqrt (((z : ℝ)-p)*((m : ℝ)-z+p+1)) := by
    rw [← Real.sqrt_mul (highestWeight_nonneg hz),
      ← Real.sqrt_mul (highestWeight_nonneg hz)]
    congr 1
    simpa only [mul_assoc] using highestWeight_step hz hp
  have hpz : z-p = (z-(p+1))+1 := by omega
  simp only [highestCoefficient, hpz, pow_succ, mul_neg_one]
  linear_combination
    ((-1 : ℝ) ^ (z-(p+1)) / Real.sqrt (highestNormalization n m z)) * he

noncomputable def limitingCoupledCoefficient (u v : ℝ) (z : ℕ) : ℕ → ℕ → ℝ
  | 0, p => limitingHighestCoefficient u v z p
  | l+1, p =>
      ((if p = 0 then 0 else Real.sqrt (p : ℝ) * v *
        limitingCoupledCoefficient u v z l (p-1)) +
      Real.sqrt ((z : ℝ)+l-p+1) * u * limitingCoupledCoefficient u v z l p) /
        Real.sqrt ((l : ℝ)+1)

open Polynomial

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_TensorSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

lemma ladderStep_sq (n : ℕ) (p : Fin n) :
    ladderStep n p ^ 2 = ((p.val : ℝ)+1) * ((n : ℝ)-p.val) := by
  have h : (p.val : ℝ) ≤ n := by exact_mod_cast p.isLt.le
  exact Real.sq_sqrt (mul_nonneg (by positivity) (by linarith))

noncomputable def raising (n : ℕ) : Module.End ℝ (Fin (n+1) → ℝ) where
  toFun x := Fin.lastCases 0 (fun p => ladderStep n p * x p.succ)
  map_add' x y := by
    funext p
    cases p using Fin.lastCases <;> simp [mul_add]
  map_smul' r x := by
    funext p
    cases p using Fin.lastCases <;> simp [mul_left_comm]

@[simp] lemma raising_castSucc (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin n) :
    raising n x p.castSucc = ladderStep n p * x p.succ := by simp [raising]
@[simp] lemma raising_last (n : ℕ) (x : Fin (n+1) → ℝ) :
    raising n x (Fin.last n) = 0 := by simp [raising]

lemma raising_lowering_apply (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    raising n (lowering n x) p =
      (((p.val : ℝ)+1) * ((n : ℝ)-p.val)) * x p := by
  cases p using Fin.lastCases with
  | last => simp
  | cast p =>
    rw [raising_castSucc, lowering_succ, ← mul_assoc, ← pow_two, ladderStep_sq]
    rfl

lemma lowering_raising_apply (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    lowering n (raising n x) p =
      ((p.val : ℝ) * ((n : ℝ)-p.val+1)) * x p := by
  cases p using Fin.cases with
  | zero => simp
  | succ p =>
    rw [lowering_succ, raising_castSucc, ← mul_assoc, ← pow_two, ladderStep_sq]
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem raising_lowering_commutator (n : ℕ) (x : Fin (n+1) → ℝ) :
    raising n (lowering n x) = lowering n (raising n x) + weight n x := by
  funext p
  simp only [raising_lowering_apply, lowering_raising_apply, Pi.add_apply, weight_apply]
  ring

theorem weight_lowering_commutator (n : ℕ) (x : Fin (n+1) → ℝ) :
    weight n (lowering n x) = lowering n (weight n x) - (2 : ℝ) • lowering n x := by
  funext p
  cases p using Fin.cases with
  | zero => simp
  | succ p =>
    simp only [weight_apply, lowering_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring

theorem lowering_raising_dot (n : ℕ) (x y : Fin (n+1) → ℝ) :
    dotProduct (lowering n x) y = dotProduct x (raising n y) := by
  unfold dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [lowering_zero, zero_mul, zero_add, lowering_succ, raising_last, mul_zero,
    add_zero, raising_castSucc]
  apply Finset.sum_congr rfl
  intro p hp
  ring

noncomputable def standardLadderSystem (n : ℕ) : LadderSystem (Fin (n+1)) where
  lower := lowering n
  raise := raising n
  weight := weight n
  adjoint := lowering_raising_dot n
  raise_lower := raising_lowering_commutator n
  weight_lower := weight_lowering_commutator n

namespace LadderSystem
variable {ι : Type*} [Fintype ι]

lemma raw_succ (S : LadderSystem ι) (x : ι → ℝ) (l : ℕ) :
    S.raw x (l+1) = S.lower (S.raw x l) := by rw [raw, pow_succ']; rfl

lemma weight_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hx : S.weight x = μ • x) (l : ℕ) :
    S.weight (S.raw x l) = (μ - 2*l) • S.raw x l := by
  induction l with
  | zero => simpa using hx
  | succ l ih =>
    rw [raw_succ, S.weight_lower, ih, map_smul, ← sub_smul,
      Nat.cast_add, Nat.cast_one]
    congr 1
    ring

lemma raise_raw (S : LadderSystem ι) {x : ι → ℝ} {μ : ℝ}
    (hx : S.weight x = μ • x) (he : S.raise x = 0) (l : ℕ) :
    S.raise (S.raw x (l+1)) = (((l : ℝ)+1)*(μ-l)) • S.raw x l := by
  induction l with
  | zero => simpa [raw_succ, S.raise_lower, he] using hx
  | succ l ih =>
    rw [raw_succ, S.raise_lower, ih, S.weight_raw hx (l+1), map_smul,
      ← raw_succ, ← add_smul, Nat.cast_add, Nat.cast_one]
    congr 1
    ring

theorem raw_norm_sq (S : LadderSystem ι) {x : ι → ℝ} {d l : ℕ}
    (hw : S.weight x = (d : ℝ) • x) (he : S.raise x = 0) (hl : l ≤ d+1) :
    dotProduct (S.raw x l) (S.raw x l) =
      (l.factorial : ℝ) * (d.descFactorial l : ℝ) * dotProduct x x := by
  induction l with
  | zero => simp [dotProduct]
  | succ l ih =>
    have hld : l ≤ d := by omega
    rw [raw_succ, S.adjoint, ← raw_succ, S.raise_raw hw he]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
    have hsum : (∑ i : ι, S.raw x l i *
        ((((l : ℝ)+1)*((d : ℝ)-l))*S.raw x l i)) =
        (((l : ℝ)+1)*((d : ℝ)-l)) * dotProduct (S.raw x l) (S.raw x l) := by
      simp only [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, ih (by omega), Nat.factorial_succ, Nat.descFactorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_sub hld]
    unfold dotProduct
    ring

lemma normalizationFactor_pos {d l : ℕ} (hl : l ≤ d) :
    0 < normalizationFactor d l :=
  mul_pos (by exact_mod_cast l.factorial_pos)
    (by exact_mod_cast Nat.descFactorial_pos.mpr hl)

lemma normalizationFactor_succ {d l : ℕ} (hl : l ≤ d) :
    normalizationFactor d (l+1) =
      (((l : ℝ)+1)*((d : ℝ)-l)) * normalizationFactor d l := by
  rw [normalizationFactor, Nat.factorial_succ, Nat.descFactorial_succ,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hl, Nat.cast_add, Nat.cast_one]
  unfold normalizationFactor
  ring

end LadderSystem

lemma tensor_factor_commute {ι κ : Type*} [Fintype ι]
    (A : Module.End ℝ (ι → ℝ)) (B : Module.End ℝ (κ → ℝ)) (x : (ι×κ) → ℝ) :
    onFirstEnd A (onSecondEnd B x) = onSecondEnd B (onFirstEnd A x) := by
  classical
  funext ⟨p,q⟩
  simp only [onFirstEnd_apply, onSecondEnd_apply]
  have hfun : (fun j => A (fun i => x (i,j)) p) =
      ∑ i : ι, (A (fun k => if i = k then 1 else 0) p) • (fun j => x (i,j)) := by
    funext j
    rw [A.pi_apply_eq_sum_univ (fun i => x (i,j))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, map_sum, A.pi_apply_eq_sum_univ (fun i => B (fun j => x (i,j)) q)]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma raising_apply_of_lt {n : ℕ} (x : Fin (n+1) → ℝ) (p : Fin (n+1))
    (hp : p.val < n) :
    raising n x p =
      Real.sqrt (((p.val : ℝ)+1)*((n : ℝ)-p.val)) * x ⟨p.val+1,by omega⟩ := by
  exact raising_castSucc n x ⟨p.val,hp⟩

lemma raising_apply_of_not_lt {n : ℕ} (x : Fin (n+1) → ℝ) (p : Fin (n+1))
    (hp : ¬p.val < n) : raising n x p = 0 := by
  have he : p = Fin.last n := by ext; simp only [Fin.val_last]; omega
  rw [he, raising_last]

theorem highestTensor_norm_sq {n m z : ℕ} (hz : z ≤ min n m) :
    dotProduct (highestTensor n m z) (highestTensor n m z) = 1 := by
  have hzn : z ≤ n := (le_min_iff.mp hz).1
  have hzm : z ≤ m := (le_min_iff.mp hz).2
  have hinner (p : Fin (n+1)) :
      (∑ q : Fin (m+1), highestTensor n m z (p,q) * highestTensor n m z (p,q)) =
        highestCoefficient n m z p.val ^ 2 := by
    by_cases hp : p.val ≤ z
    · let q₀ : Fin (m+1) := ⟨z-p.val, by omega⟩
      rw [Finset.sum_eq_single q₀]
      · simp only [highestTensor, show p.val+q₀.val = z by dsimp [q₀]; omega,
          ite_true, pow_two]
      · intro q hq hne
        have hne' : p.val+q.val ≠ z := by
          intro he
          apply hne
          ext
          dsimp [q₀]
          omega
        simp [highestTensor, hne']
      · simp
    · have hpz : z < p.val := by omega
      rw [highestCoefficient_eq_zero hpz, zero_pow (by omega : (2:ℕ) ≠ 0)]
      apply Finset.sum_eq_zero
      intro q hq
      simp [highestTensor, show p.val+q.val ≠ z by omega]
  unfold dotProduct
  rw [Fintype.sum_prod_type]
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun p => highestCoefficient n m z p ^ 2) (n+1)]
  calc
    _ = ∑ p ∈ Finset.range (z+1), highestCoefficient n m z p ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : z+1 ≤ n+1))
      intro p hp hpn
      simp only [Finset.mem_range, not_lt] at hpn
      rw [highestCoefficient_eq_zero (by omega : z < p), zero_pow (by omega : (2:ℕ) ≠ 0)]
    _ = 1 := highestCoefficient_sum_sq hz

lemma firstLoweringCoefficient_succ (n m z l : ℕ) (p : Fin n) :
    firstLoweringCoefficient n m z l p.succ.val =
      ladderStep n p / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l)) := by
  unfold firstLoweringCoefficient ladderStep
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  congr 2
  ring

lemma secondLoweringCoefficient_succ {n m z l : ℕ} (p : Fin (n+1)) (q : Fin m)
    (h : p.val+q.succ.val = z+(l+1)) :
    secondLoweringCoefficient n m z l p.val =
      ladderStep m q / Real.sqrt (((l : ℝ)+1)*((n : ℝ)+m-2*z-l)) := by
  have hc : (p.val : ℝ)+q.val+1 = (z : ℝ)+l+1 := by
    have he : p.val+q.val+1 = z+l+1 := by simpa [Nat.add_assoc] using h
    exact_mod_cast he
  unfold secondLoweringCoefficient ladderStep
  congr 2
  congr 1 <;> linarith

lemma secondLoweringCoefficient_last {n m z l : ℕ} {p : Fin (n+1)}
    (h : p.val = z+(l+1)) : secondLoweringCoefficient n m z l p.val = 0 := by
  have hc : (p.val : ℝ) = (z : ℝ)+l+1 := by exact_mod_cast h
  unfold secondLoweringCoefficient
  rw [show (z : ℝ)+l-p.val+1 = 0 by linarith]
  simp

noncomputable def coupledFamily (n m : ℕ) (i : CoupledIndex n m) :
    EuclideanSpace ℝ (Fin (n+1) × Fin (m+1)) :=
  WithLp.toLp 2 (coupledTensor n m i.1.val i.2.val)

theorem coupledIndex_card (n m : ℕ) : Fintype.card (CoupledIndex n m) = (n+1)*(m+1) := by
  let k := min n m
  have hz (z : Fin (k+1)) : 2*z.val ≤ n+m := by
    have hzn : z.val ≤ n := (Nat.le_of_lt_succ z.isLt).trans (min_le_left n m)
    have hzm : z.val ≤ m := (Nat.le_of_lt_succ z.isLt).trans (min_le_right n m)
    omega
  have hdim (z : Fin (k+1)) : ((n+m-2*z.val+1 : ℕ) : ℝ) =
      (n : ℝ)+m-2*z.val+1 := by
    rw [Nat.cast_add, Nat.cast_sub (hz z), Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_ofNat]
  have hid : (∑ z : Fin (k+1), (z.val : ℝ))*2 = ((k : ℝ)+1)*k := by
    rw [Fin.sum_univ_eq_sum_range]
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Finset.sum_range_id_mul_two (k+1))
    simpa only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using h
  simp only [CoupledIndex, Fintype.card_sigma, Fintype.card_fin]
  apply Nat.cast_injective (R := ℝ)
  change ((∑ z : Fin (k+1), (n+m-2*z.val+1) : ℕ) : ℝ) = (((n+1)*(m+1) : ℕ) : ℝ)
  rw [Nat.cast_sum]
  simp only [hdim, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  rcases le_total n m with h | h
  · have hk : (k : ℝ) = n := by exact_mod_cast min_eq_left h
    nlinarith
  · have hk : (k : ℝ) = m := by exact_mod_cast min_eq_right h
    nlinarith

end LaughlinGap.Spin

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

lemma onFirstMap_onSecond {ι κ σ : Type*} [Fintype ι]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (B : Module.End ℝ (σ → ℝ)) (x : (ι × σ) → ℝ) :
    onFirstMap A (onSecondEnd B x) = onSecondEnd B (onFirstMap A x) := by
  classical
  funext ⟨p,q⟩
  simp only [onFirstMap_apply, onSecondEnd_apply]
  have hfun : (fun j => A (fun i => x (i,j)) p) =
      ∑ i : ι, (A (fun k => if i = k then 1 else 0) p) • (fun j => x (i,j)) := by
    funext j
    rw [A.pi_apply_eq_sum_univ (fun i => x (i,j))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, map_sum, A.pi_apply_eq_sum_univ (fun i => B (fun j => x (i,j)) q)]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end LaughlinGap.Spin

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

noncomputable def orbitalPairCoefficient (Q r l : ℕ) (a : PairLabel (Q+1)) : ℝ :=
  Real.sqrt 2 * coupledTensor Q Q r l (a.val.1,a.val.2)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation Filter Topology

noncomputable def pairFactorInclusion (Q n r : ℕ)
    (x : (Fin (n+1) × Fin (2*Q-2*r+1)) → ℝ) :
    (Fin (n+1) × PairLabel (Q+1)) → ℝ := fun pa =>
  ∑ k : Fin (2*Q-2*r+1), x (pa.1,k) * orbitalPairCoefficient Q r k.val pa.2

noncomputable def fourBodyCoupled (Q D T r : ℕ) :
    (Fin (2*Q-2+1) × PairLabel (Q+1)) → ℝ :=
  pairFactorInclusion Q (2*Q-2) r
    (coupledTensor (2*Q-2) (2*Q-2*r) (D-r) (T-D))

noncomputable def fourBodyCoefficient (Q D T r p j k : ℕ) : ℝ :=
  if r ≤ j+k ∧ p+j+k=T then
    Real.sqrt 2 * coupledCoefficient Q Q r (j+k-r) j *
      coupledCoefficient (2*Q-2) (2*Q-2*r) (D-r) (T-D) p
  else 0

noncomputable def fourBodyHighestFamily (Q D : ℕ) (r : FourCopy D) :
    EuclideanSpace ℝ (Fin (2*Q-2+1) × PairLabel (Q+1)) :=
  WithLp.toLp 2 (fourBodyCoupled Q D D r.val.val)

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_NestedSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Nested Spin. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

lemma onSecondMap_onFirst {ι κ σ : Type*} [Fintype ι]
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) (B : Module.End ℝ (σ → ℝ)) (x : (σ × ι) → ℝ) :
    onSecondMap A (onFirstEnd B x) = onFirstEnd B (onSecondMap A x) := by
  classical
  funext ⟨p,q⟩
  simp only [onSecondMap_apply, onFirstEnd_apply]
  have hfun : (fun j => A (fun i => x (j,i)) q) =
      ∑ i : ι, (A (fun k => if i = k then 1 else 0) q) • (fun j => x (j,i)) := by
    funext j
    rw [A.pi_apply_eq_sum_univ (fun i => x (j,i))]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, map_sum, A.pi_apply_eq_sum_univ (fun i => B (fun j => x (j,i)) p)]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

noncomputable def nestedTensor (n m k r z l : ℕ) :
    (Fin (n+1) × (Fin (m+1) × Fin (k+1))) → ℝ :=
  fun a => ∑ q : Fin (m+k-2*r+1),
    coupledTensor n (m+k-2*r) z l (a.1,q) * coupledTensor m k r q.val a.2

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

@[simp] lemma combination_single {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (B : ι → Matrix κ κ ℝ)
    (i : ι) : combination B (Pi.single i 1) = B i := by
  simp [combination, Pi.single_apply, ite_smul]

end LaughlinGap.RealOccupation

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

noncomputable def threeWeightCoefficient (Q z T p : ℕ) : ℝ :=
  if z ≤ T then coupledCoefficient (2*Q-2) Q z (T-z) p else 0

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Spectrum. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

@[simp] lemma highestCoefficient_zero_zero (n m : ℕ) : highestCoefficient n m 0 0 = 1 := by
  simp [highestCoefficient, highestNormalization, highestWeight]

end LaughlinGap.Spin

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

def cycleIndex (ι : Type*) : ThreeIndex ι ≃ ThreeIndex ι where
  toFun t := ((t.1.2,t.2),t.1.1)
  invFun t := ((t.2,t.1.1),t.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def cycleMap (ι : Type*) : Module.End ℝ (ThreeIndex ι → ℝ) where
  toFun x t := x (cycleIndex ι t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma cycleMap_apply {ι : Type*} (x : ThreeIndex ι → ℝ) (i j k : ι) :
    cycleMap ι x ((i,j),k) = x ((j,k),i) := rfl

@[simp] lemma cycleMap_cube {ι : Type*} (x : ThreeIndex ι → ℝ) :
    cycleMap ι (cycleMap ι (cycleMap ι x)) = x := rfl

def cyclicSum (ι : Type*) : Module.End ℝ (ThreeIndex ι → ℝ) :=
  LinearMap.id + cycleMap ι + (cycleMap ι).comp (cycleMap ι)

@[simp] lemma cyclicSum_apply {ι : Type*} (x : ThreeIndex ι → ℝ) :
    cyclicSum ι x = x + cycleMap ι x + cycleMap ι (cycleMap ι x) := rfl

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_WedgeIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Wedge Identification. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct
open Occupation

def tupleThreeEquiv (ι : Type*) : ThreeIndex ι ≃ (Fin 3 → ι) where
  toFun t := ![t.1.1,t.1.2,t.2]
  invFun a := ((a 0,a 1),a 2)
  left_inv _ := rfl
  right_inv a := by ext i; fin_cases i <;> rfl

end LaughlinGap.Spin

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_ThreeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Three Comparison. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open Averaging Spin Filter Topology

noncomputable def threeWeightCoefficientStar (z T p : ℕ) : ℝ :=
  if z ≤ T then monomialWeight T p *
    (couplingPolynomial (1/Real.sqrt 3) (Real.sqrt 2 / Real.sqrt 3) z (T-z)).coeff p else 0

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

def exactRows (a : Fin 8) : RationalRow where
  t := a
  lam := (rowLambdaInteger a : ℚ)/10000000
  alpha p j := (rowAlphaInteger a p j : ℚ)/10000000

def etaRational : ℚ := ∑ a : Fin 8, (exactRows a).lam^2

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


namespace LaughlinGap.Spin
open scoped BigOperators InnerProduct

abbrev FourCoordinates (Q : ℕ) := Fin (2*Q-2+1) × Occupation.PairLabel (Q+1)

noncomputable instance instDecidableEqOrbitalTriple (D : ℕ) : DecidableEq (OrbitalTriple D) := Classical.decEq _

def orbitalTripleFinite {Q D : ℕ} (hQ : 2 ≤ Q) (hD : D ≤ Q)
    (b : OrbitalTriple D) : FourCoordinates Q :=
  (⟨b.val.1,by have := b.property; omega⟩,
    ⟨(⟨b.val.2.1,by have := b.property; omega⟩,
      ⟨b.val.2.2,by have := b.property; omega⟩),b.property.2⟩)

noncomputable def fourHighestRows (Q D : ℕ) : Matrix (FourCopy D) (OrbitalTriple D) ℝ :=
  fun r b => fourBodyCoefficient Q D D r.val.val b.val.1 b.val.2.1 b.val.2.2

end LaughlinGap.Spin

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

noncomputable def fourWeightCoefficient (Q D T r p j k : ℕ) : ℝ :=
  if D ≤ T then fourBodyCoefficient Q D T r p j k else 0

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

def fourTermP {D : ℕ} (a : FourTerm D) : ℕ := D-a.1.val

def fourTermJ {D : ℕ} (a : FourTerm D) : ℕ := a.2.1.val

def fourTermK {D : ℕ} (a : FourTerm D) : ℕ := a.1.val-a.2.1.val

def fourTermX {D : ℕ} (a : FourTerm D) : ℕ := a.2.2.val

def fourTermY {D : ℕ} (a : FourTerm D) : ℕ := D-a.1.val+1-a.2.2.val

lemma fourTerm_balance {D : ℕ} (a : FourTerm D) :
    fourTermX a+fourTermY a=fourTermP a+1 ∧
    fourTermP a+fourTermJ a+fourTermK a=D ∧
    fourTermX a<fourTermY a ∧ fourTermJ a<fourTermK a := by
  have hn := a.1.isLt
  have hj := a.2.1.isLt
  have hx := a.2.2.isLt
  dsimp [fourTermX,fourTermY,fourTermP,fourTermJ,fourTermK] at *
  omega

def fourTermLabels {D : ℕ} (hD : D ≤ 23) (a : FourTerm D) : List (Fin 25) :=
  [⟨fourTermX a,by have := fourTerm_balance a; omega⟩,
   ⟨fourTermY a,by have := fourTerm_balance a; omega⟩,
   ⟨fourTermJ a,by have := fourTerm_balance a; omega⟩,
   ⟨fourTermK a,by have := fourTerm_balance a; omega⟩]

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

def fourKeys {D : ℕ} (hD : D ≤ 23) : Finset (Finset (Fin 25)) :=
  (Finset.univ.filter (fun a : FourTerm D => (fourTermLabels hD a).Nodup)).image
    (fun a => (fourTermLabels hD a).toFinset)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_RationalFourComputable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational Four Computable. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def fourCopyEquiv (D : ℕ) : FourCopy D ≃ Fin ((D+1)/2) where
  toFun r := ⟨r.val.val/2, by have := r.val.isLt; obtain ⟨k,hk⟩ := r.property; omega⟩
  invFun i := ⟨⟨2*i.val+1,by have := i.isLt; omega⟩,⟨i.val,by rfl⟩⟩
  left_inv r := by
    apply Subtype.ext; apply Fin.ext
    have := r.property
    obtain ⟨k,hk⟩ := this
    dsimp
    omega
  right_inv i := by apply Fin.ext; dsimp; omega

@[simp] lemma fourCopyEquiv_symm_val (D : ℕ) (i : Fin ((D+1)/2)) :
    ((fourCopyEquiv D).symm i).val.val = 2*i.val+1 := rfl

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_IntegerFourRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integer Four Rows. -/

noncomputable section


namespace LaughlinGap.Spin
open scoped BigOperators

def uInt (c z T p : ℕ) : ℤ :=
  if z ≤ T then ∑ h ∈ Finset.range (p+1),
    (-1:ℤ)^(z-h) * (chooseFast z h) * (chooseFast (T-z) (p-h)) * (c:ℤ)^(p-h) else 0

end LaughlinGap.Spin
namespace LaughlinGap.RealOccupation
open scoped BigOperators
open Spin

def vInt (D T r p j k : ℕ) : ℤ :=
  if D ≤ T ∧ r ≤ j+k ∧ p+j+k=T then
    uInt 1 r (j+k) j * uInt 1 (D-r) (T-r) p else 0

def fourSumInteger (a : Fin 8) (D s : ℕ) (i k : Fin 9) : ℤ :=
  ∑ p : Fin 8, if h : p.val ≤ a.val+i.val ∧ a.val+i.val-p.val < 9 then
    rowAlphaInteger a p ⟨a.val+i.val-p.val,h.2⟩ *
      vInt D (a.val+i.val+k.val) s p.val (a.val+i.val-p.val) k.val *
        (2:ℤ)^((s+1)/2+p.val) else 0

def exactFourInteger (D u v : ℕ) : ℤ :=
  -(∑ a : Fin 8, ∑ i : Fin 9, ∑ k : Fin 9, fourRowWeight D a i k *
    fourSumInteger a D u i k * fourSumInteger a D v k i)

def exactFourEval (D u v : ℕ) : ℚ := (exactFourInteger D u v:ℚ) / fourMatrixDenominator D

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_CachedIntegerRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cached Integer Rows. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators

def integerTableEval (D : ℕ) (S : Fin ((D+1)/2) → Fin 8 → Fin 9 → Fin 9 → ℤ)
    (u v : Fin ((D+1)/2)) : ℚ :=
  ((-(∑ a : Fin 8, ∑ i : Fin 9, ∑ k : Fin 9, fourRowWeight D a i k *
    S u a i k * S v a k i):ℤ):ℚ) / fourMatrixDenominator D

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastFourKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Four Keys. -/

noncomputable section


namespace LaughlinGap.RealOccupation

def checkFourTerms (D : ℕ) (P : FourTerm D → Bool) : Bool :=
  (List.finRange (D+1)).all fun n =>
    (List.finRange ((n.val+1)/2)).all fun j =>
      (List.finRange ((D-n.val+2)/2)).all fun x => P ⟨n,j,x⟩

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

def checkFourFibersSound {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (fibers : Fin K → Finset (FourTerm D)) : Bool :=
  (List.finRange K).all fun a => @decide (∀ b ∈ fibers a,
    (fourTermLabels hD b).toFinset=keys a) (Finset.decidableDforallFinset (s := fibers a))

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FourTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four Tables. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin

variable {ι : Type*} [Fintype ι]

def tableComparison (D : ℕ) (ε : ℚ)
    (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ) :
    Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ := fun u v =>
  (if u=v then ((if 2*u.val+1=1 then 2 else 0)+ε)*copyNormalizationSq D (2*u.val+1) else 0) -
    copyNormalizationSq D (2*u.val+1) * Y u v * copyNormalizationSq D (2*v.val+1)

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table18. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable18

def sums : Fin 9 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7], ![s_6_0, s_6_1, s_6_2, s_6_3, s_6_4, s_6_5, s_6_6, s_6_7], ![s_7_0, s_7_1, s_7_2, s_7_3, s_7_4, s_7_5, s_7_6, s_7_7], ![s_8_0, s_8_1, s_8_2, s_8_3, s_8_4, s_8_5, s_8_6, s_8_7]]
end SumTable18
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate18. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate18

def fibers : Fin 39 → Finset (FourTerm 18) := ![{⟨⟨18,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨17,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨16,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨8,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨15,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨7,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨5,by decide⟩)⟩}]
end Certificate18
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table21. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable21

def sums : Fin 11 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7], ![s_6_0, s_6_1, s_6_2, s_6_3, s_6_4, s_6_5, s_6_6, s_6_7], ![s_7_0, s_7_1, s_7_2, s_7_3, s_7_4, s_7_5, s_7_6, s_7_7], ![s_8_0, s_8_1, s_8_2, s_8_3, s_8_4, s_8_5, s_8_6, s_8_7], ![s_9_0, s_9_1, s_9_2, s_9_3, s_9_4, s_9_5, s_9_6, s_9_7], ![s_10_0, s_10_1, s_10_2, s_10_3, s_10_4, s_10_5, s_10_6, s_10_7]]
end SumTable21
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table22. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable22

def sums : Fin 11 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7], ![s_6_0, s_6_1, s_6_2, s_6_3, s_6_4, s_6_5, s_6_6, s_6_7], ![s_7_0, s_7_1, s_7_2, s_7_3, s_7_4, s_7_5, s_7_6, s_7_7], ![s_8_0, s_8_1, s_8_2, s_8_3, s_8_4, s_8_5, s_8_6, s_8_7], ![s_9_0, s_9_1, s_9_2, s_9_3, s_9_4, s_9_5, s_9_6, s_9_7], ![s_10_0, s_10_1, s_10_2, s_10_3, s_10_4, s_10_5, s_10_6, s_10_7]]
end SumTable22
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate22. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate22

def representatives : Fin 72 → FourTerm 22 := ![⟨⟨22,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨22,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨21,by decide⟩,(⟨10,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨20,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨19,by decide⟩,(⟨9,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨18,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨5,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨17,by decide⟩,(⟨8,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨2,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨16,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨6,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨15,by decide⟩,(⟨7,by decide⟩,⟨3,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨4,by decide⟩)⟩]
end Certificate22
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table9. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable9

def sums : Fin 5 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7]]
end SumTable9
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table10. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable10

def sums : Fin 5 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7]]
end SumTable10
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table11. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable11

def sums : Fin 6 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7]]
end SumTable11
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table12. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable12

def sums : Fin 6 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7]]
end SumTable12
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table13. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable13

def sums : Fin 7 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7], ![s_6_0, s_6_1, s_6_2, s_6_3, s_6_4, s_6_5, s_6_6, s_6_7]]
end SumTable13
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table14. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable14

def sums : Fin 7 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7], ![s_6_0, s_6_1, s_6_2, s_6_3, s_6_4, s_6_5, s_6_6, s_6_7]]
end SumTable14
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table16. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable16

def sums : Fin 8 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7], ![s_4_0, s_4_1, s_4_2, s_4_3, s_4_4, s_4_5, s_4_6, s_4_7], ![s_5_0, s_5_1, s_5_2, s_5_3, s_5_4, s_5_5, s_5_6, s_5_7], ![s_6_0, s_6_1, s_6_2, s_6_3, s_6_4, s_6_5, s_6_6, s_6_7], ![s_7_0, s_7_1, s_7_2, s_7_3, s_7_4, s_7_5, s_7_6, s_7_7]]
end SumTable16
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table5. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable5

def sums : Fin 3 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7]]
end SumTable5
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table7. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable7

def sums : Fin 4 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7]]
end SumTable7
end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_SumTable8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum Table8. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators
namespace SumTable8

def sums : Fin 4 → Fin 8 → Fin 9 → Fin 9 → ℤ := ![![s_0_0, s_0_1, s_0_2, s_0_3, s_0_4, s_0_5, s_0_6, s_0_7], ![s_1_0, s_1_1, s_1_2, s_1_3, s_1_4, s_1_5, s_1_6, s_1_7], ![s_2_0, s_2_1, s_2_2, s_2_3, s_2_4, s_2_5, s_2_6, s_2_7], ![s_3_0, s_3_1, s_3_2, s_3_3, s_3_4, s_3_5, s_3_6, s_3_7]]
end SumTable8
end LaughlinGap.RealOccupation

end

end OAI
end


