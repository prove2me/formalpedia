-- Prove2me | solution 1 for Arxiv1606_00062.orthodir_identification
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:00:33.697022+00:00
-- url     : https://prove2.me/submissions/24ff352d-780a-474d-80f3-5751f050af33

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

set_option autoImplicit false

namespace S72OD
open Arxiv1606_00062

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma stable (A : V →L[ℂ] V) (g : V) : ∀ j i, i ≤ j → orthodirHist A g j i = orthodirHist A g i i := by
  intro j
  induction j with
  | zero => intro i hi; rw [Nat.le_zero.mp hi]
  | succ j ih =>
    intro i hi
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hij : i ≤ j := Nat.lt_succ_iff.mp h
      simp only [orthodirHist, hij, if_true]
      exact ih i hij
    · rw [le_antisymm hi h]

lemma step (A : V →L[ℂ] V) (g : V) (j : ℕ) :
    orthodirDir A g (j + 1) = A (orthodirDir A g j) +
      ∑ i ∈ Finset.range (j + 1), orthodirBeta A g i j • orthodirDir A g i := by
  unfold orthodirDir orthodirBeta
  conv_lhs => rw [orthodirHist]
  simp only [show ¬ (j + 1 ≤ j) from by omega, if_false]
  congr 1
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  unfold orthodirDir
  rw [stable A g j i hi']

lemma main (A : V →L[ℂ] V) (g : V) (j : ℕ) :
    orthodirDir A g j = (A ^ j) (orthodirDir A g 0) +
      ∑ l ∈ Finset.range j, ∑ i ∈ Finset.range (l + 1),
        orthodirBeta A g i l • (A ^ (j - 1 - l)) (orthodirDir A g i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [step, ih, map_add, map_sum, Finset.sum_range_succ (fun l => ∑ i ∈ Finset.range (l + 1),
      orthodirBeta A g i l • (A ^ (j + 1 - 1 - l)) (orthodirDir A g i))]
    have e1 : A ((A ^ j) (orthodirDir A g 0)) = (A ^ (j + 1)) (orthodirDir A g 0) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    have e2 : ∀ l ∈ Finset.range j, A (∑ i ∈ Finset.range (l + 1),
        orthodirBeta A g i l • (A ^ (j - 1 - l)) (orthodirDir A g i)) =
        ∑ i ∈ Finset.range (l + 1),
        orthodirBeta A g i l • (A ^ (j + 1 - 1 - l)) (orthodirDir A g i) := by
      intro l hl
      have hl' : l < j := Finset.mem_range.mp hl
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul, show j + 1 - 1 - l = (j - 1 - l) + 1 by omega, pow_succ',
        ContinuousLinearMap.mul_apply]
    rw [e1, Finset.sum_congr rfl e2]
    simp only [show j + 1 - 1 - j = 0 by omega, pow_zero, ContinuousLinearMap.one_apply]
    abel

end S72OD

namespace S72OI
open Arxiv1606_00062 S72OD

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def W (T : V →L[ℂ] V) (g : V) (n : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ (Set.range (fun k : Fin n => (T ^ (k : ℕ)) g))

lemma memW (T : V →L[ℂ] V) (g : V) {i n : ℕ} (h : i < n) : (T ^ i) g ∈ W T g n :=
  Submodule.subset_span ⟨⟨i, h⟩, rfl⟩

lemma monoW (T : V →L[ℂ] V) (g : V) {m n : ℕ} (h : m ≤ n) : W T g m ≤ W T g n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact memW T g (lt_of_lt_of_le k.2 h)

lemma mapW (T : V →L[ℂ] V) (g : V) (n : ℕ) {v : V} (hv : v ∈ W T g n) :
    (1 - T) v ∈ W T g (n + 1) := by
  have : W T g n ≤ (W T g (n + 1)).comap ((1 - T : V →L[ℂ] V) : V →ₗ[ℂ] V) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    show (1 - T) ((T ^ (k : ℕ)) g) ∈ W T g (n + 1)
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    have : T ((T ^ (k : ℕ)) g) = (T ^ ((k : ℕ) + 1)) g := by
      rw [pow_succ', ContinuousLinearMap.mul_apply]
    rw [this]
    exact Submodule.sub_mem _ (memW T g (by omega)) (memW T g (by omega))
  exact this hv

lemma memP (T : V →L[ℂ] V) (g : V) : ∀ j, orthodirDir (1 - T) g j ∈ W T g (j + 1) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero =>
      have : orthodirDir (1 - T) g 0 = (T ^ 0) g := by simp [orthodirDir, orthodirHist]
      rw [this]; exact memW T g (by omega)
    | succ j =>
      rw [step]
      refine Submodule.add_mem _ (mapW T g _ (ih j (by omega))) ?_
      refine Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.mp hi
      exact monoW T g (by omega) (ih i (by omega))

end S72OI

open Arxiv1606_00062 S72OD S72OI in
theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (T : V →L[ℂ] V) (g : V) :
    ∃ γ : ℕ → ℕ → ℂ,
      (∀ j : ℕ, orthodirDir (1 - T) g j =
        ∑ i ∈ Finset.range (j + 1), γ i j • msIter T g i) ∧
      (∀ j : ℕ, orthodirDir (1 - T) g (j + 1) =
        ∑ i ∈ Finset.range (j + 1), γ i j • msIter T g i -
          ∑ i ∈ Finset.range (j + 1), γ i j • msIter T g (i + 1) +
          ∑ i ∈ Finset.range (j + 1), orthodirBeta (1 - T) g i j • orthodirDir (1 - T) g i) := by
  have H : ∀ j, ∃ c : Fin (j + 1) → ℂ, ∑ k, c k • (T ^ (k : ℕ)) g = orthodirDir (1 - T) g j :=
    fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (memP T g j)
  choose c hc using H
  let γ : ℕ → ℕ → ℂ := fun i j => if h : i < j + 1 then c j ⟨i, h⟩ else 0
  have h1 : ∀ j : ℕ, orthodirDir (1 - T) g j =
      ∑ i ∈ Finset.range (j + 1), γ i j • msIter T g i := by
    intro j
    rw [← hc j, ← Fin.sum_univ_eq_sum_range (fun i => γ i j • msIter T g i)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [γ, dif_pos k.2, msIter]
  refine ⟨γ, h1, fun j => ?_⟩
  rw [step, h1 j, map_sum]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, smul_sub]
  congr 2
  simp only [msIter]
  rw [pow_succ', ContinuousLinearMap.mul_apply]
