-- Prove2me | solution 1 for AccelPPM.FPR.weak_duality_D
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:13:40.027352+00:00
-- url     : https://prove2.me/submissions/2de7cc56-f79d-496d-8b86-83f86e3160ae

import Definitions.Def_AccelPPM_FPR_IsMaximalMonotone
import Definitions.Def_AccelPPM_FPR_IsGeneralPPMSeq
import Definitions.Def_AccelPPM_FPR_IsAccelPPMSeq
import Definitions.Def_AccelPPM_FPR_kimCoeff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic
import Definitions.Def_AccelPPM_FPR_boundBD
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order
open scoped BigOperators RealInnerProductSpace MatrixOrder Matrix
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
private lemma resolvent_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (hM : IsMonotoneOp M) (lam : ℝ) (hlam : 0 < lam)
    (y x z : H) (hx : lam⁻¹ • (y-x) ∈ M x) (hz : lam⁻¹ • (y-z) ∈ M z) : x = z := by
  have hh := hM x z _ _ hx hz
  have he : lam⁻¹ • (y-x) - lam⁻¹ • (y-z) = -lam⁻¹ • (x-z) := by module
  rw [he, inner_smul_right, real_inner_self_eq_norm_sq] at hh
  have hl : 0 < lam⁻¹ := inv_pos.mpr hlam
  have hsq : ‖x-z‖^2 ≤ 0 := le_of_not_gt (fun hs => (not_lt_of_ge hh) (by nlinarith [mul_pos hl hs]))
  have hn : ‖x-z‖ = 0 := by nlinarith [norm_nonneg (x-z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)
private lemma general_prefix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsGeneralPPMSeq M lam kimCoeff x y) (i : ℕ) :
    y i = y 0 + (2/((i : ℝ)+1)) • (∑ k ∈ range i, (k+1 : ℝ) • (x (k+1)-y k)) := by
  have he : ∀ i, y i = y 0 + ∑ j ∈ range i, ∑ k ∈ range (j+1), kimCoeff (j+1) (k+1) • (x (k+1)-y k) := by
    intro i; induction i with
    | zero => simp
    | succ i ih =>
      rw [h.2 i, ih, add_assoc]
      congr 1
      exact (sum_range_succ _ _).symm
  rw [he i]
  congr 1
  convert cumulative_kim (fun k => x k-y (k-1)) i using 1 <;> simp
private lemma general_halpern {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsGeneralPPMSeq M lam kimCoeff x y) (i : ℕ) :
    y (i+1) = (1/((i : ℝ)+2)) • y 0 + (((i : ℝ)+1)/((i : ℝ)+2)) • (2 • x (i+1)-y i) := by
  rw [general_prefix M lam x y h (i+1), sum_range_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [general_prefix M lam x y h i]
  have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
  have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring
private lemma accel_identity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsAccelPPMSeq M lam x y) (i : ℕ) :
    ((i : ℝ)+1) • y i + (i : ℝ) • y (i-1) - (2*(i : ℝ)) • x i = y 0 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [h.2.2 i, ← ih]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
    match_scalars <;> field_simp <;> ring
private lemma accel_halpern {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H) (h : IsAccelPPMSeq M lam x y) (i : ℕ) :
    y (i+1) = (1/((i : ℝ)+2)) • y 0 + (((i : ℝ)+1)/((i : ℝ)+2)) • (2 • x (i+1)-y i) := by
  rw [h.2.2 i, ← accel_identity M lam x y h i]
  have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
  match_scalars <;> field_simp <;> ring
private theorem methods_coincide {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x' y' : ℕ → H) (hgen : IsGeneralPPMSeq M lam kimCoeff x' y')
    (x y : ℕ → H) (hacc : IsAccelPPMSeq M lam x y) (h0 : y' 0 = y 0) :
    (∀ i, 1 ≤ i → x' i = x i) ∧ ∀ i, y' i = y i := by
  have hy : ∀ i, y' i = y i := by
    intro i; induction i with
    | zero => exact h0
    | succ i ih =>
      have hx : x' (i+1) = x (i+1) := resolvent_unique M hM.1 lam hlam (y i) _ _
        (by simpa only [ih] using hgen.1 i) (hacc.2.1 i)
      rw [general_halpern M lam x' y' hgen i, accel_halpern M lam x y hacc i, h0, ih, hx]
  refine ⟨?_, hy⟩
  intro i hi
  have hx := resolvent_unique M hM.1 lam hlam (y (i-1)) (x' i) (x i)
    (by simpa only [Nat.sub_add_cancel hi, hy] using hgen.1 (i-1))
    (by simpa only [Nat.sub_add_cancel hi] using hacc.2.1 (i-1))
  exact hx

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
private noncomputable def liftVec {n H : Type*} [Fintype n] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : n → H) : (n → ℝ) →ₗ[ℝ] H where
  toFun u := ∑ i, u i • v i
  map_add' u w := by simp [add_smul, sum_add_distrib]
  map_smul' c u := by simp [mul_smul, smul_sum]
private noncomputable def evalMat {n H : Type*} [Fintype n] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : n → H) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun A := ∑ i, ∑ j, A i j * ⟪v i, v j⟫
  map_add' A B := by simp [add_mul, sum_add_distrib]
  map_smul' c A := by simp [mul_assoc, mul_sum]
private lemma eval_nonneg {n H : Type*} [Fintype n] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : n → H) (A : Matrix n n ℝ) (hA : A.PosSemidef) : 0 ≤ evalMat v A := by
  have hp := (hA.hadamard (Matrix.posSemidef_gram ℝ v)).dotProduct_mulVec_nonneg (fun _ => (1 : ℝ))
  simpa [evalMat, Matrix.mulVec, dotProduct, Matrix.hadamard_apply] using hp
private lemma eval_outer {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : Fin (N+1) → H) (u w : Fin (N+1) → ℝ) :
    evalMat v (Matrix.vecMulVec u w) = ⟪liftVec v u, liftVec v w⟫ := by
  simp only [evalMat, liftVec, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulVec_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  ring
private lemma eval_sym {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : Fin (N+1) → H) (u w : Fin (N+1) → ℝ) :
    evalMat v (symOuter u w) = ⟪liftVec v u, liftVec v w⟫ := by
  rw [symOuter, map_smul, map_add, eval_outer, eval_outer, real_inner_comm (liftVec v w)]
  simp only [smul_eq_mul]
  ring
private lemma lift_basis {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ℕ → H) (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N+1) :
    liftVec (fun j : Fin (N+1) => v (j.val+1)) (basisVec N i) = v i := by
  classical
  let j : Fin (N+1) := ⟨i-1, by omega⟩
  change (∑ k : Fin (N+1), (if k.val+1=i then (1:ℝ) else 0) • v (k.val+1)) = v i
  rw [sum_eq_single j]
  · simp [j, Nat.sub_add_cancel hi]
  · intro k hk hkj
    have hne : k.val+1 ≠ i := by
      intro he
      apply hkj
      apply Fin.ext
      dsimp [j]
      omega
    simp [hne]
  · simp

private lemma lift_row {N : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : ℕ → H) (h : ℕ → ℕ → ℝ) (l : ℕ) (hl : l+1 ≤ N) :
    liftVec (fun j : Fin (N+1) => v (j.val+1))
      (∑ k ∈ range (l+1), h (l+1) (k+1) • basisVec N (k+1)) =
      ∑ k ∈ range (l+1), h (l+1) (k+1) • v (k+1) := by
  simp only [map_sum, map_smul]
  apply sum_congr rfl
  intro k hk
  rw [lift_basis v (k+1) (by omega) (by have := mem_range.mp hk; omega)]
private theorem matrix_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (b c : ℝ)
    (hfeas : IsDualFeasible N h a b c) (v : ℕ → H)
    (hA : ∀ i ∈ Icc 2 N, ⟪v (i-1)-v i, v (i-1)-v i -
      ∑ k ∈ range (i-1), h (i-1) (k+1) • v (k+1)⟫ ≤ 0)
    (hB : ⟪v N, v N-v (N+1) + ∑ l ∈ range (N-1), ∑ k ∈ range (l+1), h (l+1) (k+1) • v (k+1)⟫ ≤ 0) :
    ‖v N‖^2 ≤ c*‖v (N+1)‖^2 := by
  let V : Fin (N+1) → H := fun j => v (j.val+1)
  have hEA : ∀ i ∈ Icc 2 N, evalMat V (matA N h (i-1) i) ≤ 0 := by
    intro i hi
    have hil := (mem_Icc.mp hi).1
    have hir := (mem_Icc.mp hi).2
    have he : i-1 = (i-1-1)+1 := by omega
    have hI : Ico (i-1-1) (i-1) = {i-1-1} := by rw [he, Nat.add_sub_cancel]; simp
    have hm : i-1-1+1 = i-1 := by omega
    rw [matA, hI, sum_singleton, map_sub, eval_sym, eval_sym, map_sub]
    rw [lift_basis v (i-1) (by omega) (by omega), lift_basis v i (by omega) (by omega)]
    rw [lift_row v h (i-1-1) (by omega), hm]
    simpa only [inner_sub_right] using hA i hi
  have hEB : evalMat V (matB N h N) ≤ 0 := by
    have hp : liftVec V (∑ l ∈ range (N-1), ∑ k ∈ range (l+1), h (l+1) (k+1) • basisVec N (k+1)) =
        ∑ l ∈ range (N-1), ∑ k ∈ range (l+1), h (l+1) (k+1) • v (k+1) := by
      rw [map_sum]
      apply sum_congr rfl
      intro l hl
      exact lift_row v h l (by have := mem_range.mp hl; omega)
    rw [matB, map_add, map_sub, eval_outer, eval_sym, eval_sym, hp]
    rw [lift_basis v N hN (by omega), lift_basis v (N+1) (by omega) (by omega)]
    simpa only [inner_add_right, inner_sub_right] using hB
  have hp := eval_nonneg V (dualMatrix N h a b c) hfeas.2.2.2
  rw [dualMatrix, map_sub, map_add, map_add, map_sum, map_smul, map_smul, eval_outer,
    matC, eval_outer, lift_basis v N hN (by omega), lift_basis v (N+1) (by omega) (by omega)] at hp
  simp only [real_inner_self_eq_norm_sq, smul_eq_mul, map_smul] at hp
  have hsum : (∑ i ∈ Icc 2 N, a i * evalMat V (matA N h (i-1) i)) ≤ 0 :=
    sum_nonpos fun i hi => mul_nonpos_of_nonneg_of_nonpos (hfeas.1 i hi) (hEA i hi)
  have hb := mul_nonpos_of_nonneg_of_nonpos hfeas.2.1 hEB
  nlinarith

private lemma general_row {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (h : ℕ → ℕ → ℝ) (x y : ℕ → H)
    (hseq : IsGeneralPPMSeq M lam h x y) (i : ℕ) :
    (∑ k ∈ range (i+1), h (i+1) (k+1) • (y k-x (k+1))) = y i-y (i+1) := by
  rw [hseq.2 i]
  simp only [sub_eq_add_neg, smul_add, smul_neg, sum_add_distrib, sum_neg_distrib]
  abel
private lemma general_prefix_any {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (h : ℕ → ℕ → ℝ) (x y : ℕ → H)
    (hseq : IsGeneralPPMSeq M lam h x y) (i : ℕ) :
    (∑ l ∈ range i, ∑ k ∈ range (l+1), h (l+1) (k+1) • (y k-x (k+1))) = y 0-y i := by
  induction i with
  | zero => simp
  | succ i ih => rw [sum_range_succ, ih, general_row M lam h x y hseq i]; abel
private lemma residual_mono {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (hM : IsMonotoneOp M) (lam : ℝ) (hlam : 0 < lam)
    (h : ℕ → ℕ → ℝ) (x y : ℕ → H) (hseq : IsGeneralPPMSeq M lam h x y)
    (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    0 ≤ ⟪(y (i-1)-x i)-(y (j-1)-x j), x i-x j⟫ := by
  have hp := hM (x i) (x j) _ _
    (by simpa only [Nat.sub_add_cancel hi] using hseq.1 (i-1))
    (by simpa only [Nat.sub_add_cancel hj] using hseq.1 (j-1))
  rw [← smul_sub, inner_smul_right] at hp
  rw [← real_inner_comm (x i-x j)] at hp
  exact nonneg_of_mul_nonneg_right hp (inv_pos.mpr hlam)
private theorem weak_duality {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (b c : ℝ)
    (hfeas : IsDualFeasible N h a b c)
    (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x y : ℕ → H) (hseq : IsGeneralPPMSeq M lam h x y)
    (xstar : H) (hxstar : xstar ∈ zeroSet M) (R : ℝ) (hR : 0 < R)
    (hy0 : ‖y 0-xstar‖ ≤ R) : ‖x N-y (N-1)‖^2/R^2 ≤ c := by
  let v : ℕ → H := fun i => if i=N+1 then y 0-xstar else y (i-1)-x i
  have hv : ∀ i, i ≤ N → v i = y (i-1)-x i := by
    intro i hi
    simp [v, show i ≠ N+1 by omega]
  have hva : v (N+1) = y 0-xstar := by simp [v]
  have hr : ∀ l, l+1 ≤ N →
      (∑ k ∈ range (l+1), h (l+1) (k+1) • v (k+1)) = y l-y (l+1) := by
    intro l hl
    convert general_row M lam h x y hseq l using 1
    apply sum_congr rfl
    intro k hk
    rw [hv (k+1) (by have := mem_range.mp hk; omega), Nat.add_sub_cancel]
  have hp := matrix_bound N hN h a b c hfeas v ?_ ?_
  · rw [hv N le_rfl, hva, norm_sub_rev (y (N-1)) (x N)] at hp
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mpr
    calc
      ‖x N-y (N-1)‖^2 ≤ c*‖y 0-xstar‖^2 := hp
      _ ≤ c*R^2 := mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) (le_of_lt hR) |>.mpr hy0) hfeas.2.2.1
  · intro i hi
    have hil := (mem_Icc.mp hi).1
    have hir := (mem_Icc.mp hi).2
    have hm : i-1-1+1 = i-1 := by omega
    have hh := hr (i-1-1) (by omega)
    rw [hm] at hh
    rw [hv (i-1) (by omega), hv i hir, hh]
    have he : (y (i-1-1)-x (i-1))-(y (i-1)-x i)-(y (i-1-1)-y (i-1)) = -(x (i-1)-x i) := by abel
    rw [he, inner_neg_right]
    exact neg_nonpos.mpr (residual_mono M hM.1 lam hlam h x y hseq (i-1) i (by omega) (by omega))
  · have hs : (∑ l ∈ range (N-1), ∑ k ∈ range (l+1), h (l+1) (k+1) • v (k+1)) = y 0-y (N-1) := by
      rw [← general_prefix_any M lam h x y hseq (N-1)]
      apply sum_congr rfl
      intro l hl
      rw [hr l (by have := mem_range.mp hl; omega), general_row M lam h x y hseq l]
    rw [hv N le_rfl, hva, hs]
    have he : (y (N-1)-x N)-(y 0-xstar)+(y 0-y (N-1)) = -(x N-xstar) := by abel
    rw [he, inner_neg_right]
    apply neg_nonpos.mpr
    have hh := hM.1 (x N) xstar _ 0
      (by simpa only [Nat.sub_add_cancel hN] using hseq.1 (N-1)) hxstar
    simp only [sub_zero, inner_smul_right] at hh
    rw [← real_inner_comm (x N-xstar)] at hh
    exact nonneg_of_mul_nonneg_right hh (inv_pos.mpr hlam)
private lemma halpern_general {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (lam : ℝ) (x y : ℕ → H)
    (hp : ∀ i, lam⁻¹ • (y i-x (i+1)) ∈ M (x (i+1)))
    (hh : ∀ i, y (i+1) = (1/((i : ℝ)+2)) • y 0 + (((i : ℝ)+1)/((i : ℝ)+2)) • (2 • x (i+1)-y i)) :
    IsGeneralPPMSeq M lam kimCoeff x y := by
  have pref : ∀ i, y i = y 0 + (2/((i : ℝ)+1)) • (∑ k ∈ range i, (k+1 : ℝ) • (x (k+1)-y k)) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [hh i, sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [ih]
      have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
      have hi2 : (i : ℝ)+2 ≠ 0 := by positivity
      match_scalars <;> field_simp <;> ring
  have pref' : ∀ i, y i = y 0 + ∑ l ∈ range i, ∑ k ∈ range (l+1), kimCoeff (l+1) (k+1) • (x (k+1)-y k) := by
    intro i
    rw [pref i]
    congr 1
    convert (cumulative_kim (fun k => x k-y (k-1)) i).symm using 1 <;> simp
  refine ⟨hp, ?_⟩
  intro i
  calc
    y (i+1) = y 0 + ((∑ l ∈ range i, ∑ k ∈ range (l+1), kimCoeff (l+1) (k+1) • (x (k+1)-y k)) +
        ∑ k ∈ range (i+1), kimCoeff (i+1) (k+1) • (x (k+1)-y k)) := by
      rw [pref' (i+1)]
      congr 1
      exact sum_range_succ _ _
    _ = y i + ∑ k ∈ range (i+1), kimCoeff (i+1) (k+1) • (x (k+1)-y k) := by rw [pref' i]; abel
private theorem general_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : ℕ) (hN : 1 ≤ N) (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x y : ℕ → H) (hseq : IsGeneralPPMSeq M lam kimCoeff x y)
    (xstar : H) (hxstar : xstar ∈ zeroSet M) (R : ℝ) (hR : 0 < R) (hy0 : ‖y 0-xstar‖ ≤ R) :
    ((‖x N-y (N-1)‖^2/R^2 : ℝ) : EReal) ≤ boundBD N kimCoeff ∧
    boundBD N kimCoeff ≤ ((1/(N : ℝ)^2 : ℝ) : EReal) := by
  constructor
  · apply le_sInf
    rintro z ⟨c, ⟨a,b,hf⟩, rfl⟩
    change ((‖x N-y (N-1)‖^2/R^2 : ℝ) : EReal) ≤ (c : EReal)
    exact_mod_cast weak_duality N hN kimCoeff a b c hf M hM lam hlam x y hseq xstar hxstar R hR hy0
  · exact sInf_le ⟨1/(N : ℝ)^2, ⟨_, _, dual_feasible N hN⟩, rfl⟩
private theorem accel_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x y : ℕ → H) (hseq : IsAccelPPMSeq M lam x y)
    (xstar : H) (hxstar : xstar ∈ zeroSet M) (R : ℝ) (hR : 0 < R) (hx0 : ‖x 0-xstar‖ ≤ R) :
    ∀ i : ℕ, 1 ≤ i → ‖x i-y (i-1)‖^2 ≤ R^2/(i : ℝ)^2 := by
  intro i hi
  have hg := halpern_general M lam x y hseq.2.1 (accel_halpern M lam x y hseq)
  have hb := weak_duality i hi kimCoeff _ _ _ (dual_feasible i hi) M hM lam hlam x y hg xstar hxstar R hR
    (by simpa only [← hseq.1] using hx0)
  have hRR : 0 < R^2 := sq_pos_of_pos hR
  have hb' := (div_le_iff₀ hRR).mp hb
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hb'
end PPMProof

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (N : ℕ) (hN : 1 ≤ N) (h : ℕ → ℕ → ℝ) (a : ℕ → ℝ) (b c : ℝ)
    (hfeas : IsDualFeasible N h a b c)
    (M : H → Set H) (hM : IsMaximalMonotone M) (lam : ℝ) (hlam : 0 < lam)
    (x y : ℕ → H) (hseq : IsGeneralPPMSeq M lam h x y)
    (xstar : H) (hxstar : xstar ∈ zeroSet M) (R : ℝ) (hR : 0 < R)
    (hy0 : ‖y 0 - xstar‖ ≤ R) :
    ‖x N - y (N - 1)‖ ^ 2 / R ^ 2 ≤ c := by
  exact PPMProof.weak_duality N hN h a b c hfeas M hM lam hlam x y hseq xstar hxstar R hR hy0
