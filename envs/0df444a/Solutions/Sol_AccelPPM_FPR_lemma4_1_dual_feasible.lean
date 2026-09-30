-- Prove2me | solution 1 for AccelPPM.FPR.lemma4_1_dual_feasible
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:08:25.607331+00:00
-- url     : https://prove2.me/submissions/303c25c0-ae72-457d-85a0-d3bf2bd0b402

import Definitions.Def_AccelPPM_FPR_IsMaximalMonotone
import Definitions.Def_AccelPPM_FPR_IsGeneralPPMSeq
import Definitions.Def_AccelPPM_FPR_IsAccelPPMSeq
import Definitions.Def_AccelPPM_FPR_kimCoeff
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_AccelPPM_FPR_boundBD
import Mathlib.Tactic
open scoped BigOperators RealInnerProductSpace
open Finset AccelPPM.FPR
namespace PPMProof
private lemma kim_row {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℕ → E)
    (i : ℕ) (hi : 1 ≤ i) :
    (∑ k ∈ range i, kimCoeff i (k+1) • v (k+1)) =
      (2*(i : ℝ)/((i : ℝ)+1)) • v i -
      (2/((i : ℝ)*((i : ℝ)+1))) • (∑ k ∈ range (i-1), (k+1 : ℝ) • v (k+1)) := by
  have he : i = (i-1)+1 := by omega
  conv_lhs => rw [he]
  rw [sum_range_succ]
  simp only [Nat.sub_add_cancel hi]
  have hs : ∀ k ∈ range (i-1), kimCoeff i (k+1) = -(2/((i : ℝ)*((i : ℝ)+1)))*(k+1 : ℝ) := by
    intro k hk
    have hki : k+1 ≠ i := by have := mem_range.mp hk; omega
    simp only [kimCoeff, if_neg hki, Nat.cast_add, Nat.cast_one]
    ring
  have hS : (∑ k ∈ range (i-1), kimCoeff i (k+1) • v (k+1)) =
      -(2/((i : ℝ)*((i : ℝ)+1))) • (∑ k ∈ range (i-1), (k+1 : ℝ) • v (k+1)) := by
    rw [smul_sum]
    apply sum_congr rfl
    intro k hk
    rw [hs k hk, mul_smul]
  rw [hS]
  simp [kimCoeff]
  module
private lemma cumulative_kim {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ℕ → E) (i : ℕ) :
    (∑ j ∈ range i, ∑ k ∈ range (j+1), kimCoeff (j+1) (k+1) • v (k+1)) =
      (2/((i : ℝ)+1)) • (∑ k ∈ range i, (k+1 : ℝ) • v (k+1)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [sum_range_succ, ih, kim_row v (i+1) (by omega)]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, sum_range_succ]
    have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
    have hi2 : (i : ℝ)+1+1 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
private noncomputable def potential (N i : ℕ) : Matrix (Fin (N+1)) (Fin (N+1)) ℝ :=
  (2*(i : ℝ)*((i : ℝ)-1)) • Matrix.vecMulVec (basisVec N i) (basisVec N i) -
    4 • symOuter (basisVec N i) (∑ k ∈ range (i-1), (k+1 : ℝ) • basisVec N (k+1))
private lemma weighted_A (N i : ℕ) (hi : 2 ≤ i) :
    (2*((i : ℝ)-1)*(i : ℝ)) • matA N kimCoeff (i-1) i = potential N i - potential N (i-1) := by
  have he : i-1 = (i-1-1)+1 := by omega
  have hI : Ico (i-1-1) (i-1) = {i-1-1} := by rw [he, Nat.add_sub_cancel]; simp
  unfold matA
  rw [hI, sum_singleton]
  have hm : i-1-1+1 = i-1 := by omega
  rw [hm, kim_row (basisVec N) (i-1) (by omega)]
  unfold potential
  conv_rhs => lhs; arg 2; arg 2; rw [he, sum_range_succ]
  simp only [Nat.sub_add_cancel (by omega : 1 ≤ i-1)]
  have hcast : ((i-1 : ℕ) : ℝ) = (i : ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hcast2 : ((i-1-1 : ℕ) : ℝ) = (i : ℝ)-2 := by rw [Nat.cast_sub (by omega), hcast]; norm_num; ring
  have hip : (i : ℝ) ≠ 0 := by positivity
  have him : (i : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ i := by exact_mod_cast hi
    linarith
  ext p q
  simp only [symOuter, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hcast, hcast2]
  ring_nf
  field_simp [show (-1+(i : ℝ)) ≠ 0 by linarith]
  ring
private lemma sum_weighted_A (N n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ Icc 2 n, (2*((i : ℝ)-1)*(i : ℝ)) • matA N kimCoeff (i-1) i) = potential N n := by
  induction n, hn using Nat.le_induction with
  | base => ext p q; simp [potential, symOuter, Matrix.vecMulVec]
  | succ n hn ih =>
    rw [sum_Icc_succ_top (by omega), ih, weighted_A N (n+1) (by omega)]
    simp only [Nat.add_sub_cancel]
    abel
private lemma dual_factor (N : ℕ) (hN : 1 ≤ N) :
    dualMatrix N kimCoeff (fun i => 2*((i : ℝ)-1)*(i : ℝ)/(N : ℝ)^2) (2/(N : ℝ)) (1/(N : ℝ)^2) =
      Matrix.vecMulVec (basisVec N N - (1/(N : ℝ)) • basisVec N (N+1))
        (basisVec N N - (1/(N : ℝ)) • basisVec N (N+1)) := by
  have hS : (∑ i ∈ Icc 2 N, (2*((i : ℝ)-1)*(i : ℝ)/(N : ℝ)^2) • matA N kimCoeff (i-1) i) =
      (1/(N : ℝ)^2) • potential N N := by
    rw [← sum_weighted_A N N hN, smul_sum]
    apply sum_congr rfl
    intro i hi
    rw [smul_smul]
    congr 1
    ring
  unfold dualMatrix
  rw [hS]
  unfold matB
  rw [cumulative_kim (basisVec N) (N-1)]
  have hcast : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by rw [Nat.cast_sub hN]; norm_num
  have hNp : (N : ℝ) ≠ 0 := by positivity
  ext p q
  simp only [potential, matC, symOuter, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hcast]
  ring_nf
  field_simp
  ring
private theorem dual_feasible (N : ℕ) (hN : 1 ≤ N) :
    IsDualFeasible N kimCoeff (fun i => 2*((i : ℝ)-1)*(i : ℝ)/(N : ℝ)^2)
      (2/(N : ℝ)) (1/(N : ℝ)^2) := by
  refine ⟨?_, by positivity, by positivity, ?_⟩
  · intro i hi
    have : (2 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Nat.cast_nonneg _)) (sq_nonneg _)
  · rw [dual_factor N hN]
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext p q
      simp [Matrix.conjTranspose_apply, Matrix.vecMulVec, mul_comm]
    · intro z
      simp only [Matrix.vecMulVec_mulVec, dotProduct_smul, star_trivial, smul_eq_mul]
      rw [dotProduct_comm z]
      exact mul_self_nonneg _
end PPMProof

theorem solution (N : ℕ) (hN : 1 ≤ N) :
    IsDualFeasible N kimCoeff (fun i => 2 * ((i : ℝ) - 1) * (i : ℝ) / (N : ℝ) ^ 2)
      (2 / (N : ℝ)) (1 / (N : ℝ) ^ 2) := by
  exact PPMProof.dual_feasible N hN
