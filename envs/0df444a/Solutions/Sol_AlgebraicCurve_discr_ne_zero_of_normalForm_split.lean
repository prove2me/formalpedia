-- Prove2me | solution 1 for AlgebraicCurve.discr_ne_zero_of_normalForm_split
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bc189574-f953-51fe-9290-e8320958c660

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_discr_ne_zero_of_normalForm_split

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Polynomial Matrix

universe u v

noncomputable section

namespace DiscSplitSol

theorem coeff_prod_of_natDegree_le {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R[X]) (N : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ N i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, N i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, N i) = ∏ i ∈ s, (f i).coeff (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h' : ∀ i ∈ s, (f i).natDegree ≤ N i := fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨ih1, ih2⟩ := ih h'
    have hfa := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (Nat.add_le_add hfa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hfa ih1, ih2]

section Main

variable {K : Type u} [Field K] {n : ℕ} {B : Type v} [CommRing B] [Algebra K[X] B]

theorem main (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (τ : Fin (n + 1) → Fin (n + 1) → K) (hτu : IsUnit (Matrix.det (Matrix.of τ)))
    (hτ0 : ∀ j, τ j 0 = 1)
    (hτm : ∀ j i i', i ≠ 0 → i' ≠ 0 →
      τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    Algebra.discr K[X] b ≠ 0 := by
  classical

  set γ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K[X] := fun i j k => b.repr (b i * b j) k
    with hγdef
  have hγ0 : ∀ j k, γ 0 j k = if j = k then 1 else 0 := fun j k => by
    simp only [hγdef, hb0, one_mul, b.repr_self, Finsupp.single_apply]
  have hγc : ∀ i j k, γ i j k = γ j i k := fun i j k => by simp only [hγdef, mul_comm]
  have hdle : ∀ m, d m ≤ 2 := fun m => by
    by_cases hm : m = 0
    · rw [hm, hd0]; exact Nat.zero_le _
    · rcases hd m hm with h | h <;> omega
  have hdge : ∀ m, m ≠ 0 → 1 ≤ d m := fun m hm => by rcases hd m hm with h | h <;> omega

  have hdegAll : ∀ x y z, (γ x y z).natDegree ≤ d x + d y - d z := by
    intro x y z
    by_cases hx : x = 0
    · subst hx; rw [hγ0]; split_ifs <;> simp
    by_cases hy : y = 0
    · subst hy; rw [hγc, hγ0]; split_ifs <;> simp
    exact hdeg x y z hx hy

  have hvan : ∀ x y z, d x + d y < d z → γ x y z = 0 := by
    intro x y z hlt
    by_cases hx : x = 0
    · subst hx; rw [hγ0]; split_ifs with h
      · subst h; rw [hd0] at hlt; omega
      · rfl
    by_cases hy : y = 0
    · subst hy; rw [hγc, hγ0]; split_ifs with h
      · subst h; rw [hd0] at hlt; omega
      · rfl
    have := hdle z; have := hdge x hx; have := hdge y hy
    omega

  set c : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → K := fun x y z => (γ x y z).coeff (d x + d y - d z)
    with hcdef
  have hc0 : ∀ y z, c 0 y z = if y = z then 1 else 0 := by
    intro y z
    simp only [hcdef, hγ0, hd0, zero_add]
    split_ifs with h
    · subst h; simp
    · simp
  have hcc : ∀ x y z, c x y z = c y x z := fun x y z => by
    simp only [hcdef, hγc x y z, Nat.add_comm (d x) (d y)]

  have hτm' : ∀ j i i', τ j i * τ j i' = ∑ k, c i i' k * τ j k := by
    intro j i i'
    by_cases hi : i = 0
    · subst hi
      rw [hτ0, one_mul]
      simp only [hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    by_cases hi' : i' = 0
    · subst hi'
      rw [hτ0, mul_one]
      simp only [hcc i 0, hc0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    exact hτm j i i' hi hi'

  have htr : ∀ x : B, Algebra.trace K[X] B x = ∑ m, b.repr (x * b m) m := by
    intro x
    rw [Algebra.trace_eq_matrix_trace b x, Matrix.trace]
    simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  have hM : ∀ i k, Algebra.traceMatrix K[X] b i k = ∑ m, ∑ l, γ i k l * γ l m m := by
    intro i k
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, htr]
    refine Finset.sum_congr rfl fun m _ => ?_

    conv_lhs => rw [← b.sum_repr (b i * b k), Finset.sum_mul, map_sum]
    rw [Finset.sum_apply']
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, map_smul, Finsupp.smul_apply, smul_eq_mul]

  have hterm : ∀ i k l m, (γ i k l * γ l m m).natDegree ≤ d i + d k ∧
      (γ i k l * γ l m m).coeff (d i + d k) = c i k l * c l m m := by
    intro i k l m
    by_cases hlt : d i + d k < d l
    · rw [hvan i k l hlt]
      simp only [zero_mul, natDegree_zero, coeff_zero]
      refine ⟨Nat.zero_le _, ?_⟩
      simp only [hcdef, hvan i k l hlt, coeff_zero, zero_mul]
    · have h1 : (γ i k l).natDegree ≤ d i + d k - d l := hdegAll i k l
      have h2 : (γ l m m).natDegree ≤ d l := by
        have := hdegAll l m m; rwa [Nat.add_sub_cancel] at this
      have hsum : d i + d k - d l + d l = d i + d k := by omega
      refine ⟨natDegree_mul_le.trans (by omega), ?_⟩
      rw [← hsum, coeff_mul_add_eq_of_natDegree_le h1 h2]
      simp only [hcdef, Nat.add_sub_cancel]
  have hMdeg : ∀ i k, (Algebra.traceMatrix K[X] b i k).natDegree ≤ d i + d k := by
    intro i k
    rw [hM]
    exact natDegree_sum_le_of_forall_le _ _ fun m _ =>
      natDegree_sum_le_of_forall_le _ _ fun l _ => (hterm i k l m).1
  have hMtop : ∀ i k, (Algebra.traceMatrix K[X] b i k).coeff (d i + d k) =
      ∑ m, ∑ l, c i k l * c l m m := by
    intro i k
    rw [hM, finsetSum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [finsetSum_coeff]
    exact Finset.sum_congr rfl fun l _ => (hterm i k l m).2

  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of τ with hTdef
  have htrace : ∀ l, ∑ m, c l m m = ∑ j, τ j l := by
    intro l
    let Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun m l' => c l l' m
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.diagonal fun j => τ j l
    have hTL : T * Λ = D * T := by
      ext j l'
      rw [Matrix.mul_apply, Matrix.diagonal_mul]
      change ∑ m, τ j m * c l l' m = τ j l * τ j l'
      rw [hτm' j l l']
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    have hΛ : Λ = T⁻¹ * D * T := by
      rw [Matrix.mul_assoc, ← hTL, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul T hτu,
        Matrix.one_mul]
    have h1 : Matrix.trace Λ = ∑ m, c l m m := by
      simp only [Matrix.trace, Matrix.diag, Λ, Matrix.of_apply]
    rw [← h1, hΛ, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv T hτu, Matrix.one_mul,
      Matrix.trace_diagonal]
  have hMtop' : ∀ i k, (Algebra.traceMatrix K[X] b i k).coeff (d i + d k) = (Tᵀ * T) i k := by
    intro i k
    rw [hMtop, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hTdef, Matrix.of_apply]
    calc ∑ m, ∑ l, c i k l * c l m m = ∑ l, c i k l * ∑ m, c l m m := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
      _ = ∑ l, c i k l * ∑ j, τ j l := Finset.sum_congr rfl fun l _ => by rw [htrace]
      _ = ∑ j, ∑ l, c i k l * τ j l := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun l _ => by rw [Finset.mul_sum]
      _ = ∑ j, τ j i * τ j k := Finset.sum_congr rfl fun j _ => (hτm' j i k).symm

  set Dtot : ℕ := ∑ i, d i + ∑ i, d i with hDtot
  have hdet : (Algebra.discr K[X] b).coeff Dtot = (Tᵀ * T).det := by
    rw [Algebra.discr_def, Matrix.det_apply, Matrix.det_apply, finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    rw [← C_eq_intCast, coeff_C_mul]
    congr 1
    have hσsum : ∑ i, (d (σ i) + d i) = Dtot := by
      rw [Finset.sum_add_distrib, hDtot]
      congr 1
      exact Equiv.sum_comp σ d
    have := (coeff_prod_of_natDegree_le Finset.univ
      (fun i => Algebra.traceMatrix K[X] b (σ i) i) (fun i => d (σ i) + d i)
      (fun i _ => hMdeg (σ i) i)).2
    rw [hσsum] at this
    rw [this]
    exact Finset.prod_congr rfl fun i _ => hMtop' (σ i) i
  have hdetne : (Tᵀ * T).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    have hne : T.det ≠ 0 := hτu.ne_zero
    exact mul_ne_zero hne hne
  intro hzero
  apply hdetne
  rw [← hdet, hzero, coeff_zero]

end Main

end DiscSplitSol

end

theorem solution
    (K : Type u) [Field K] (n : ℕ) (B : Type v) [CommRing B] [Algebra K[X] B]
    (b : Module.Basis (Fin (n + 1)) K[X] B) (d : Fin (n + 1) → ℕ)
    (hb0 : b 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((b.repr (b i * b j)) k).natDegree ≤ d i + d j - d k)
    (hinf : ∃ τ : Fin (n + 1) → Fin (n + 1) → K,
      IsUnit (Matrix.det (Matrix.of τ)) ∧
      (∀ j, τ j 0 = 1) ∧
      ∀ j i i', i ≠ 0 → i' ≠ 0 →
        τ j i * τ j i' = ∑ k, ((b.repr (b i * b i')) k).coeff (d i + d i' - d k) * τ j k) :
    Algebra.discr K[X] b ≠ 0 := by
  obtain ⟨τ, hτu, hτ0, hτm⟩ := hinf
  exact DiscSplitSol.main b d hb0 hd0 hd hdeg τ hτu hτ0 hτm

end S_AlgebraicCurve_discr_ne_zero_of_normalForm_split
end P2MW
export P2MW.S_AlgebraicCurve_discr_ne_zero_of_normalForm_split (solution)
