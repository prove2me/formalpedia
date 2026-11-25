-- Prove2me | solution 1 for Arxiv0812_1178.pseudo_phase_data_model
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:22:09.728191+00:00
-- url     : https://prove2.me/submissions/29a19299-afb8-4260-8703-21b5a133fbb6

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic
import Theorems.Thm_Arxiv0812_1178_wrapped_kernel_closure

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178
open scoped RealInnerProductSpace

private lemma baselineOp_mulVec (n : ℕ) (v : Fin n → ℝ) (b : Baseline n) :
    (baselineOp n *ᵥ v) b = v b.1.2 - v b.1.1 := by
  simp [baselineOp, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]

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

private lemma closureOp_mul_closurePinv {n : ℕ} (hn : 3 ≤ n) :
    closureOp n * closurePinv n = 1 := by
  have hdet : IsUnit (closureOp n * (closureOp n)ᵀ).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv_ne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hctv : (closureOp n)ᵀ *ᵥ v = 0 := by
      have hdot : ((closureOp n)ᵀ *ᵥ v) ⬝ᵥ ((closureOp n)ᵀ *ᵥ v) = 0 := by
        have h1 : v ⬝ᵥ ((closureOp n * (closureOp n)ᵀ) *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at h1
        exact h1
      ext b
      have hnonneg : ∀ x ∈ (Finset.univ : Finset (Baseline n)),
          0 ≤ ((closureOp n)ᵀ *ᵥ v) x * ((closureOp n)ᵀ *ᵥ v) x :=
        fun x _ => mul_self_nonneg _
      have hsum : ∑ x : Baseline n, ((closureOp n)ᵀ *ᵥ v) x * ((closureOp n)ᵀ *ᵥ v) x = 0 := hdot
      have hb := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum b (Finset.mem_univ b)
      exact mul_self_eq_zero.mp hb
    apply hv_ne
    ext c
    let u : Baseline n → ℝ := fun b => if b.1 = c.1 then 1 else 0
    have hCu : closureOp n *ᵥ u = Pi.single c 1 := by
      ext c'
      rw [closureOp_mulVec (by omega)]
      have hc0 : c.1.1.1 ≠ 0 := Nat.ne_of_gt c.2.1
      have hne1 : ((⟨0, by omega⟩, c'.1.1) : Fin n × Fin n) ≠ c.1 := by
        intro h; exact hc0 (congr_arg (fun p => p.1.1) h).symm
      have hne3 : ((⟨0, by omega⟩, c'.1.2) : Fin n × Fin n) ≠ c.1 := by
        intro h; exact hc0 (congr_arg (fun p => p.1.1) h).symm
      simp only [u, hne1, hne3, ↓reduceIte, zero_add, sub_zero, Pi.single_apply]
      by_cases hcc : c' = c
      · subst hcc; simp
      · have hne2 : c'.1 ≠ c.1 := fun h => hcc (Subtype.ext h)
        simp [hcc, hne2]
    have hvc : v ⬝ᵥ (closureOp n *ᵥ u) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hctv, zero_dotProduct]
    rw [hCu, dotProduct_single, mul_one] at hvc
    exact hvc
  rw [closurePinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet]

theorem solution {n : ℕ} (hn : 3 ≤ n) {P : Type*} [Fintype P]
    (H : Matrix (Baseline n) P ℂ) (x : P → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (βrand : Ω → EuclideanSpace ℝ (ClosureIdx n)) (hβm : Measurable βrand)
    (Rβ : Matrix (ClosureIdx n) (ClosureIdx n) ℝ) (hRβ : Rβ.PosSemidef)
    (hβg : Pr.map βrand = multivariateGaussian 0 Rβ) :
    (∀ (βdata βnoise : ClosureIdx n → ℝ) (κ : ClosureIdx n → ℤ),
      βdata = closureOp n *ᵥ objPhase H x + βnoise + (fun c => 2 * Real.pi * κ c) →
      pseudoPhase n βdata =
          objPhase H x + kerPhase n (objPhase H x) κ + closurePinv n *ᵥ βnoise ∧
        closureOp n *ᵥ kerPhase n (objPhase H x) κ = (fun c => 2 * Real.pi * κ c) ∧
        ∃ (α : Fin (n - 1) → ℝ) (κ' : Baseline n → ℤ),
          pseudoPhase n βdata = objPhase H x + baselineOpBar n *ᵥ α + closurePinv n *ᵥ βnoise +
            (fun b => 2 * Real.pi * κ' b)) ∧
    (∀ b, ∫ ω, (closurePinv n *ᵥ fun c => βrand ω c) b ∂Pr = 0) ∧
    (∀ b b', covariance (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b)
        (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b') Pr =
      (closurePinv n * Rβ * (closurePinv n)ᵀ) b b') ∧
    (closurePinv n * Rβ * (closurePinv n)ᵀ).det = 0 := by
  have hCCdag : closureOp n * closurePinv n = 1 := closureOp_mul_closurePinv hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro βdata βnoise κ hβ
    have h1 : pseudoPhase n βdata =
        objPhase H x + kerPhase n (objPhase H x) κ + closurePinv n *ᵥ βnoise := by
      simp only [pseudoPhase, kerPhase, hβ, Matrix.mulVec_add, Matrix.sub_mulVec,
        Matrix.one_mulVec, Matrix.mulVec_mulVec]
      ext b
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    have h2 : closureOp n *ᵥ kerPhase n (objPhase H x) κ = fun c => 2 * Real.pi * κ c := by
      simp only [kerPhase, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_sub,
        ← Matrix.mul_assoc, hCCdag, Matrix.one_mul, Matrix.mul_one, sub_self,
        Matrix.zero_mulVec, Matrix.one_mulVec, zero_add]
    have h3 : ∃ (α : Fin (n - 1) → ℝ) (κ' : Baseline n → ℤ),
        pseudoPhase n βdata = objPhase H x + baselineOpBar n *ᵥ α + closurePinv n *ᵥ βnoise +
          (fun b => 2 * Real.pi * κ' b) := by
      obtain ⟨α, κ', hker⟩ :=
        (wrapped_kernel_closure hn).2.2 (kerPhase n (objPhase H x) κ) ⟨κ, h2⟩
      refine ⟨α, κ', ?_⟩
      rw [h1, hker]
      ext b
      simp only [Pi.add_apply]
      ring
    exact ⟨h1, h2, h3⟩
  · intro b
    let xvec : EuclideanSpace ℝ (ClosureIdx n) := WithLp.toLp 2 (fun c => closurePinv n b c)
    have hfn : (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b) =
        fun ω => ⟪xvec, βrand ω⟫ := by
      ext ω
      simp only [Matrix.mulVec, dotProduct, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial, xvec]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [hfn]
    have hcont : Continuous (fun u : EuclideanSpace ℝ (ClosureIdx n) => ⟪xvec, u⟫) :=
      continuous_const.inner continuous_id
    rw [← integral_map hβm.aemeasurable hcont.aestronglyMeasurable, hβg]
    have hlin := (innerSL ℝ xvec).integral_comp_id_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian 0 Rβ))
    simpa [innerSL_apply_apply, integral_id_multivariateGaussian] using hlin
  · intro b b'
    let xvec : EuclideanSpace ℝ (ClosureIdx n) := WithLp.toLp 2 (fun c => closurePinv n b c)
    let yvec : EuclideanSpace ℝ (ClosureIdx n) := WithLp.toLp 2 (fun c => closurePinv n b' c)
    have hfn1 : (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b) =
        (fun u : EuclideanSpace ℝ (ClosureIdx n) => ⟪xvec, u⟫) ∘ βrand := by
      ext ω
      simp only [Function.comp_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, xvec]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    have hfn2 : (fun ω => (closurePinv n *ᵥ fun c => βrand ω c) b') =
        (fun u : EuclideanSpace ℝ (ClosureIdx n) => ⟪yvec, u⟫) ∘ βrand := by
      ext ω
      simp only [Function.comp_apply, Matrix.mulVec, dotProduct, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, yvec]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [hfn1, hfn2]
    have hcont1 : Continuous (fun u : EuclideanSpace ℝ (ClosureIdx n) => ⟪xvec, u⟫) :=
      continuous_const.inner continuous_id
    have hcont2 : Continuous (fun u : EuclideanSpace ℝ (ClosureIdx n) => ⟪yvec, u⟫) :=
      continuous_const.inner continuous_id
    rw [← covariance_map hcont1.aestronglyMeasurable hcont2.aestronglyMeasurable hβm.aemeasurable,
      hβg, ← covarianceBilin_apply_eq_cov (IsGaussian.memLp_two_id),
      covarianceBilin_multivariateGaussian hRβ]
    simp only [xvec, yvec, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
    ring
  · let v : Baseline n → ℝ := baselineOp n *ᵥ Pi.single ⟨0, by omega⟩ (1 : ℝ)
    have hv_ne : v ≠ 0 := by
      intro h
      let b0 : Baseline n := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩
      have hb0 := congr_fun h b0
      simp only [v, baselineOp_mulVec, Pi.zero_apply] at hb0
      have hne : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by
        intro heq; have := congr_arg Fin.val heq; simp at this
      simp [b0, hne] at hb0
    have hCv : closureOp n *ᵥ v = 0 := by
      ext c
      rw [closureOp_mulVec (by omega)]
      simp only [v, baselineOp_mulVec, Pi.zero_apply]
      ring
    have hCdagTv : (closurePinv n)ᵀ *ᵥ v = 0 := by
      rw [closurePinv, Matrix.transpose_mul, Matrix.transpose_transpose,
        ← Matrix.mulVec_mulVec, hCv, Matrix.mulVec_zero]
    have hMv : (closurePinv n * Rβ * (closurePinv n)ᵀ) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec, hCdagTv, Matrix.mulVec_zero]
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv_ne, hMv⟩
