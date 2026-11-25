-- Prove2me | solution 1 for Arxiv0812_1178.piston_invariant_factors_through_closure
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:32:02.75418+00:00
-- url     : https://prove2.me/submissions/7c12eff1-9b41-4118-88e5-e61c1c496978

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic
import Theorems.Thm_Arxiv0812_1178_closure_kernel_eq_baseline_range

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178

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

theorem solution {n : ℕ} (hn : 3 ≤ n) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Baseline n → ℝ) → E) (hf : ContDiff ℝ 1 f)
    (hpiston : ∀ (φ : Baseline n → ℝ) (varpi : Fin n → ℝ), f (φ + baselineOp n *ᵥ varpi) = f φ) :
    ∃ g : (ClosureIdx n → ℝ) → E, ContDiff ℝ 1 g ∧ ∀ φ, f φ = g (closureOp n *ᵥ φ) := by
  let Slin : (ClosureIdx n → ℝ) →ₗ[ℝ] (Baseline n → ℝ) :=
    { toFun := fun β b => if hb : 0 < b.1.1.1 then β ⟨b.1, ⟨hb, b.2⟩⟩ else 0
      map_add' := fun β₁ β₂ => by
        ext b
        by_cases hb : 0 < b.1.1.1 <;> simp [hb]
      map_smul' := fun r β => by
        ext b
        by_cases hb : 0 < b.1.1.1 <;> simp [hb] }
  let S : (ClosureIdx n → ℝ) →L[ℝ] (Baseline n → ℝ) := Slin.toContinuousLinearMap
  refine ⟨fun β => f (S β), hf.comp S.contDiff, ?_⟩
  intro φ
  have hCS : ∀ β : ClosureIdx n → ℝ, closureOp n *ᵥ S β = β := by
    intro β
    ext c
    rw [closureOp_mulVec (by omega)]
    have h0 : ¬ (0 < (0 : ℕ)) := lt_irrefl 0
    simp only [S, LinearMap.coe_toContinuousLinearMap', Slin, LinearMap.coe_mk, AddHom.coe_mk,
      h0, ↓reduceDIte, zero_add, sub_zero, c.2.1]
  have hdiff : φ - S (closureOp n *ᵥ φ) ∈ LinearMap.ker (closureOp n).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, hCS, sub_self]
  have hker := (closure_kernel_eq_baseline_range hn).2.2.2.1
  rw [hker, LinearMap.mem_range] at hdiff
  rcases hdiff with ⟨ϖ, hϖ⟩
  rw [Matrix.mulVecLin_apply] at hϖ
  have hφ_eq : φ = S (closureOp n *ᵥ φ) + baselineOp n *ᵥ ϖ := by
    ext b
    have hb := congr_fun hϖ b
    simp only [Pi.sub_apply] at hb
    simp only [Pi.add_apply]
    linarith
  conv_lhs => rw [hφ_eq]
  exact hpiston (S (closureOp n *ᵥ φ)) ϖ
