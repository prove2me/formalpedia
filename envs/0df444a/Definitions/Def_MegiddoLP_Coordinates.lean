-- Prove2me | Definitions.Def_MegiddoLP_Coordinates
-- name    : MegiddoLP_Coordinates
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T21:11:40.218212+00:00
-- url     : https://prove2.me/theorems/6fa2e3e2-3463-4530-9e83-d1569f51469f
-- title:
--   A Vandermonde change of coordinates for fixed-dimension linear programming
-- statement:
--   Bounds on coefficient magnitudes determine an invertible moment-curve basis with all coordinates of every nonzero row nonzero. The change of coordinates preserves feasibility.
-- source:
--   Nimrod Megiddo, Linear Programming in Linear Time When the Dimension Is Fixed, JACM 31(1), 1984, §3.2, p. 119. https://theory.stanford.edu/~megiddo/pdf/lplin.pdf

import Definitions.Def_Polyhedron
import Definitions.Def_MegiddoLP_CoefficientScan
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Set

namespace MegiddoLP.FixedDim

open Matrix LinearOptimization SmaleNinth MachineDSL

/-- From a positive lower bound on nonzero magnitudes and an upper bound on all
magnitudes, choose a common interval of moment-curve parameters for all rows. -/
theorem momentCurve_dot_ne_zero_of_bounds {d : ℕ} (a : Fin d → ℝ) (ha : a ≠ 0)
    {lo hi t : ℝ} (hlo₁ : lo ≤ 1) (hhi : 1 ≤ hi)
    (hlower : ∀ j, a j ≠ 0 → lo ≤ |a j|) (hupper : ∀ j, |a j| ≤ hi)
    (ht : 0 < t) (htbound : t ≤ lo / (2 * ((d : ℝ) + 1) * hi)) :
    a ⬝ᵥ (fun j : Fin d => t ^ j.val) ≠ 0 := by
  classical
  let support := Finset.univ.filter fun j : Fin d => a j ≠ 0
  have hne : support.Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    exact ⟨j, by simpa [support] using hj⟩
  obtain ⟨k, hk, hmin⟩ := Finset.exists_min_image support Fin.val hne
  have hkn : a k ≠ 0 := (Finset.mem_filter.mp hk).2
  have hbefore : ∀ j : Fin d, j.val < k.val → a j = 0 := by
    intro j hj
    by_contra hjn
    exact (not_le_of_gt hj) (hmin j (by simpa [support] using hjn))
  have hhi₀ : 0 < hi := lt_of_lt_of_le zero_lt_one hhi
  have hden : 0 < 2 * ((d : ℝ) + 1) * hi := by positivity
  have ht₁ : t ≤ 1 := htbound.trans ((div_le_iff₀ hden).2 (by
    have hd : 0 ≤ (d : ℝ) := by positivity
    nlinarith [mul_nonneg hd hhi₀.le]))
  let term (j : Fin d) := a j * t ^ (j.val - k.val)
  have hfactor :
      a ⬝ᵥ (fun j : Fin d => t ^ j.val) = t ^ k.val * ∑ j, term j := by
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : k.val ≤ j.val
    · have hej : j.val = k.val + (j.val - k.val) := by omega
      simp only [term]
      rw [mul_left_comm, ← pow_add, ← hej]
    · simp [term, hbefore j (lt_of_not_ge hj)]
  have hmain : term k = a k := by simp [term]
  have hterm (j : Fin d) (hj : j ≠ k) : |term j| ≤ hi * t := by
    by_cases hj' : j.val < k.val
    · simp [term, hbefore j hj', mul_nonneg hhi₀.le ht.le]
    · have hkj : k.val < j.val :=
        (le_of_not_gt hj').lt_of_ne (fun h => hj (Fin.val_injective h.symm))
      have hpow : t ^ (j.val - k.val) ≤ t := by
        simpa using (pow_le_pow_of_le_one ht.le ht₁ (show 1 ≤ j.val - k.val by omega))
      change |a j * t ^ (j.val - k.val)| ≤ hi * t
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht.le _)]
      exact mul_le_mul (hupper j) hpow (pow_nonneg ht.le _) hhi₀.le
  let tail := ∑ j ∈ Finset.univ.erase k, term j
  have htail : |tail| < lo := calc
    |tail| ≤ ∑ j ∈ Finset.univ.erase k, |term j| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _j ∈ Finset.univ.erase k, hi * t :=
      Finset.sum_le_sum fun j hj => hterm j (Finset.mem_erase.mp hj).1
    _ ≤ (d : ℝ) * (hi * t) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hhi₀.le ht.le)
      exact_mod_cast (Finset.card_le_univ (Finset.univ.erase k)).trans_eq (Fintype.card_fin d)
    _ < lo := by
      have hprod := (le_div_iff₀ hden).mp htbound
      have hpos : 0 < hi * t := mul_pos hhi₀ ht
      have hnonneg : 0 ≤ (d : ℝ) * (hi * t) := by positivity
      nlinarith only [hprod, hpos, hnonneg]
  rw [hfactor, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hmain]
  intro hz
  have heq : tail = -a k := by
    have hs := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ht.ne')
    change tail + a k = 0 at hs
    linarith
  rw [heq, abs_neg] at htail
  exact (not_lt_of_ge (hlower k hkn)) htail

/-- A Vandermonde change of coordinates computed from two bounds on the
coefficients. Every nonzero input row has a nonzero entry in every coordinate. -/
theorem vandermonde_basis_of_bounds {n d : ℕ} (a : Fin n → Fin d → ℝ)
    {lo hi : ℝ} (hlo : 0 < lo) (hlo₁ : lo ≤ 1) (hhi : 1 ≤ hi)
    (hlower : ∀ i j, a i j ≠ 0 → lo ≤ |a i j|)
    (hupper : ∀ i j, |a i j| ≤ hi) :
    let δ := lo / (2 * ((d : ℝ) + 1) * hi)
    let t := fun j : Fin d => δ * ((j.val : ℝ) + 1) / ((d : ℝ) + 1)
    let M := (Matrix.vandermonde t)ᵀ
    IsUnit M.det ∧ ∀ i j, a i ≠ 0 → (Mᵀ *ᵥ a i) j ≠ 0 := by
  dsimp only
  set δ := lo / (2 * ((d : ℝ) + 1) * hi)
  set t : Fin d → ℝ := fun j => δ * ((j.val : ℝ) + 1) / ((d : ℝ) + 1)
  have hhi₀ : 0 < hi := zero_lt_one.trans_le hhi
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : 0 < (d : ℝ) + 1 := by positivity
  constructor
  · rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    intro hz
    obtain ⟨j, k, heq, hne⟩ := Matrix.det_vandermonde_eq_zero_iff.mp hz
    have heq' := (div_left_inj' hd.ne').mp heq
    have hjk := mul_left_cancel₀ hδ.ne' heq'
    exact hne (Fin.val_injective (by exact_mod_cast add_right_cancel hjk))
  · intro i j ha
    rw [Matrix.transpose_transpose]
    have hval : (Matrix.vandermonde t *ᵥ a i) j =
        a i ⬝ᵥ (fun k : Fin d => t j ^ k.val) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    rw [hval]
    apply momentCurve_dot_ne_zero_of_bounds (a i) ha hlo₁ hhi (hlower i) (hupper i)
    · dsimp [t]; positivity
    · change t j ≤ δ
      apply (div_le_iff₀ hd).mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.succ_le_succ j.isLt.le) hδ.le

/-- Invertible changes of coordinates preserve LP feasibility. -/
theorem changeBasis_feasible_iff {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : IsUnit M.det) :
    (polyhedron (A * M) b).Nonempty ↔ (polyhedron A b).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨M *ᵥ y, ?_⟩
    simpa only [polyhedron, Set.mem_ofPred_eq, Matrix.mulVec_mulVec] using hy
  · rintro ⟨x, hx⟩
    refine ⟨M⁻¹ *ᵥ x, ?_⟩
    simp only [polyhedron, Set.mem_ofPred_eq] at hx ⊢
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec x M M⁻¹,
      Matrix.mul_nonsing_inv M hM, Matrix.one_mulVec]
    exact hx

/-- A machine scan computes a scalar from which the Vandermonde basis is
determined. The basis preserves feasibility and removes zero coordinates
from every nonzero row. -/
theorem scan_for_basis_runs {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) :
    ∃ t : MState,
      Runs (scanCoefficients d) ⟨fun _ => 0, fun _ => 0, encodeLP A b⟩ t
        ((12 * d + 7) * (n + 1)) ∧ t.mem = encodeLP A b ∧
      let lo := t.regs 2
      let hi := 1 / lo
      let δ := lo / (2 * ((d : ℝ) + 1) * hi)
      let M := (Matrix.vandermonde fun j : Fin d =>
        δ * ((j.val : ℝ) + 1) / ((d : ℝ) + 1))ᵀ
      IsUnit M.det ∧ ((polyhedron (A * M) b).Nonempty ↔ (polyhedron A b).Nonempty) ∧
        ∀ i j, A i ≠ 0 → (A * M) i j ≠ 0 := by
  obtain ⟨t, hrun, hmem, hlo, hlo₁, hbounds⟩ := scanCoefficients_runs A b
  have hhi : 1 ≤ 1 / t.regs 2 := (le_div_iff₀ hlo).2 (by simpa only [one_mul] using hlo₁)
  obtain ⟨hM, hrow⟩ := vandermonde_basis_of_bounds A hlo hlo₁ hhi
    (fun i j => (hbounds i j).1) (fun i j => (hbounds i j).2)
  refine ⟨t, hrun, hmem, hM, changeBasis_feasible_iff A b _ hM, ?_⟩
  intro i j hi
  rw [Matrix.mul_apply_eq_vecMul, ← Matrix.mulVec_transpose]
  exact hrow i j hi

end MegiddoLP.FixedDim


