-- Prove2me | solution 1 for Arxiv0812_1178.wrapped_kernel_closure
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:21:03.530584+00:00
-- url     : https://prove2.me/submissions/a2f2ce9b-cf39-4156-9321-dc7e7c85499f

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic
import Theorems.Thm_Arxiv0812_1178_closure_kernel_eq_baseline_range

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178

private lemma baselineOp_mulVec (n : ℕ) (v : Fin n → ℝ) (b : Baseline n) :
    (baselineOp n *ᵥ v) b = v b.1.2 - v b.1.1 := by
  simp [baselineOp, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

private lemma baselineOpBar_mulVec {n : ℕ} (hn : 1 ≤ n) (α : Fin (n - 1) → ℝ) (b : Baseline n) :
    (baselineOpBar n *ᵥ α) b =
      (if h2 : 0 < b.1.2.1 then α ⟨b.1.2.1 - 1, by have := b.1.2.2; omega⟩ else 0) -
      (if h1 : 0 < b.1.1.1 then α ⟨b.1.1.1 - 1, by have := b.1.1.2; omega⟩ else 0) := by
  have hsum : ∀ x : Fin n,
      (∑ j : Fin (n - 1), (if (⟨j.1 + 1, by have := j.2; omega⟩ : Fin n) = x then (1 : ℝ) else 0) * α j) =
      if hx : 0 < x.1 then α ⟨x.1 - 1, by have := x.2; omega⟩ else 0 := by
    intro x
    by_cases hx : 0 < x.1
    · rw [dif_pos hx]
      let j0 : Fin (n - 1) := ⟨x.1 - 1, by have := x.2; omega⟩
      have hiff : ∀ j : Fin (n - 1),
          ((⟨j.1 + 1, by have := j.2; omega⟩ : Fin n) = x) ↔ j = j0 := by
        intro j
        constructor
        · intro h
          have hval : j.1 + 1 = x.1 := congr_arg Fin.val h
          exact Fin.ext (by show j.1 = x.1 - 1; omega)
        · rintro rfl
          exact Fin.ext (by show x.1 - 1 + 1 = x.1; omega)
      simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rfl
    · rw [dif_neg hx]
      have hfalse : ∀ j : Fin (n - 1), (⟨j.1 + 1, by have := j.2; omega⟩ : Fin n) ≠ x := by
        intro j h
        have hval : j.1 + 1 = x.1 := congr_arg Fin.val h
        omega
      simp [hfalse]
  simp only [baselineOpBar, baselineOp, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib,
    hsum]

private lemma closureOp_mulVec {n : ℕ} (hn : 1 ≤ n) (φ : Baseline n → ℝ) (c : ClosureIdx n) :
    (closureOp n *ᵥ φ) c =
      φ ⟨(⟨0, by omega⟩, c.1.1), c.2.1⟩ +
      φ ⟨c.1, c.2.2⟩ -
      φ ⟨(⟨0, by omega⟩, c.1.2), lt_trans c.2.1 c.2.2⟩ := by
  let b1 : Baseline n := ⟨(⟨0, by omega⟩, c.1.1), c.2.1⟩
  let b2 : Baseline n := ⟨c.1, c.2.2⟩
  let b3 : Baseline n := ⟨(⟨0, by omega⟩, c.1.2), lt_trans c.2.1 c.2.2⟩
  have h1 : ∀ b : Baseline n, (b.1.1.1 = 0 ∧ b.1.2 = c.1.1) ↔ b = b1 := by
    intro b
    constructor
    · rintro ⟨h0, h2⟩; exact Subtype.ext (Prod.ext (Fin.ext h0) h2)
    · rintro rfl; exact ⟨rfl, rfl⟩
  have h2 : ∀ b : Baseline n, b.1 = c.1 ↔ b = b2 := by
    intro b
    constructor
    · intro h; exact Subtype.ext h
    · rintro rfl; rfl
  have h3 : ∀ b : Baseline n, (b.1.1.1 = 0 ∧ b.1.2 = c.1.2) ↔ b = b3 := by
    intro b
    constructor
    · rintro ⟨h0, h2⟩; exact Subtype.ext (Prod.ext (Fin.ext h0) h2)
    · rintro rfl; exact ⟨rfl, rfl⟩
  simp only [closureOp, Matrix.mulVec, dotProduct, h1, h2, h3, sub_mul, add_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

theorem solution {n : ℕ} (hn : 3 ≤ n) :
    LinearMap.range (baselineOp n).mulVecLin = LinearMap.range (baselineOpBar n).mulVecLin ∧
    LinearMap.ker (closureOp n).mulVecLin = LinearMap.range (baselineOpBar n).mulVecLin ∧
    ∀ φker : Baseline n → ℝ,
      (∃ k : ClosureIdx n → ℤ, closureOp n *ᵥ φker = fun c => 2 * Real.pi * k c) →
      ∃ (α : Fin (n - 1) → ℝ) (κ : Baseline n → ℤ),
        φker = baselineOpBar n *ᵥ α + fun b => 2 * Real.pi * κ b := by
  have hrange : LinearMap.range (baselineOp n).mulVecLin =
      LinearMap.range (baselineOpBar n).mulVecLin := by
    ext φ
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨ϖ, rfl⟩
      refine ⟨fun j => ϖ ⟨j.1 + 1, by have := j.2; omega⟩ - ϖ ⟨0, by omega⟩, ?_⟩
      ext b
      rw [baselineOpBar_mulVec (by omega), baselineOp_mulVec]
      have hb2 : 0 < b.1.2.1 := lt_of_le_of_lt (Nat.zero_le _) b.2
      simp only [dif_pos hb2]
      have hidx2 : (⟨b.1.2.1 - 1 + 1, by have := b.1.2.2; omega⟩ : Fin n) = b.1.2 :=
        Fin.ext (by simp; omega)
      rw [hidx2]
      by_cases hb1 : 0 < b.1.1.1
      · simp only [dif_pos hb1]
        have hidx1 : (⟨b.1.1.1 - 1 + 1, by have := b.1.1.2; omega⟩ : Fin n) = b.1.1 :=
          Fin.ext (by simp; omega)
        rw [hidx1]
        ring
      · simp only [dif_neg hb1, sub_zero]
        have hidx1 : (⟨0, by omega⟩ : Fin n) = b.1.1 := Fin.ext (by simp; omega)
        rw [hidx1]
    · rintro ⟨α, rfl⟩
      refine ⟨fun j => if hj : 0 < j.1 then α ⟨j.1 - 1, by have := j.2; omega⟩ else 0, ?_⟩
      ext b
      rw [baselineOp_mulVec, baselineOpBar_mulVec (by omega)]
  have hker_eq : LinearMap.ker (closureOp n).mulVecLin =
      LinearMap.range (baselineOp n).mulVecLin :=
    (closure_kernel_eq_baseline_range hn).2.2.2.1
  have hker_bar : LinearMap.ker (closureOp n).mulVecLin =
      LinearMap.range (baselineOpBar n).mulVecLin :=
    hker_eq.trans hrange
  refine ⟨hrange, hker_bar, ?_⟩
  rintro φker ⟨k, hk⟩
  let κ : Baseline n → ℤ := fun b => if hb : 0 < b.1.1.1 then k ⟨b.1, ⟨hb, b.2⟩⟩ else 0
  have hκ : closureOp n *ᵥ (fun b => 2 * Real.pi * κ b) = fun c => 2 * Real.pi * k c := by
    ext c
    rw [closureOp_mulVec (by omega)]
    have h0 : ¬ (0 < (0 : ℕ)) := lt_irrefl 0
    simp only [κ, h0, ↓reduceDIte, Int.cast_zero, mul_zero, zero_add, sub_zero, c.2.1]
  have hdiff : φker - (fun b => 2 * Real.pi * κ b) ∈ LinearMap.ker (closureOp n).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hk, hκ, sub_self]
  rw [hker_bar, LinearMap.mem_range] at hdiff
  rcases hdiff with ⟨α, hα⟩
  refine ⟨α, κ, ?_⟩
  rw [Matrix.mulVecLin_apply] at hα
  ext b
  have := congr_fun hα b
  simp only [Pi.sub_apply] at this
  simp only [Pi.add_apply]
  linarith
