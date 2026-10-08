-- Prove2me | solution 1 for AronszajnRK.Inclusion.dominated_partialOrder
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T06:56:13.020994+00:00
-- url     : https://prove2.me/submissions/8b65950e-7278-4c81-a9e1-32fdb172e855

import Mathlib
import Definitions.Def_AronszajnRK_Limits_KernelLE

/-!
# Aronszajn §7: `≪` is a partial order on positive matrices

Transitivity: sums of positive matrices are positive, and `K₃ − K₁` is the pointwise sum of
`K₃ − K₂` and `K₂ − K₁`.  Antisymmetry: if both `K₂ − K₁` and `K₁ − K₂` are positive, all
quadratic forms of the difference vanish; testing on `single x 1` kills the diagonal and on
`single x 1 + single y 1`, `single x 1 + single y i` the off-diagonal entries.
-/

open scoped ComplexOrder

namespace AronszajnRK.Inclusion

/-- Entries of a Hermitian kernel matrix. -/
lemma herm_entries {X : Type*} (D : X → X → ℂ) (h : (Matrix.of D).IsHermitian) :
    ∀ i j, star (D j i) = D i j := by
  intro i j
  simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using
    congrArg (fun M : Matrix X X ℂ => M i j) h.eq

/-- A kernel matrix with Hermitian entries is Hermitian. -/
lemma herm_of_entries {X : Type*} (D : X → X → ℂ) (h : ∀ i j, star (D j i) = D i j) :
    (Matrix.of D).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  exact h i j

/-- Quadratic forms are additive in the kernel. -/
lemma qf_add {X : Type*} (P Q : X → X → ℂ) (b : X →₀ ℂ) :
    b.sum (fun i bi => b.sum (fun j bj => star bi * (P i j + Q i j) * bj))
      = b.sum (fun i bi => b.sum (fun j bj => star bi * P i j * bj))
        + b.sum (fun i bi => b.sum (fun j bj => star bi * Q i j * bj)) := by
  classical
  simp only [Finsupp.sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Quadratic forms of the negated kernel. -/
lemma qf_neg {X : Type*} (P : X → X → ℂ) (b : X →₀ ℂ) :
    b.sum (fun i bi => b.sum (fun j bj => star bi * (-P i j) * bj))
      = -b.sum (fun i bi => b.sum (fun j bj => star bi * P i j * bj)) := by
  classical
  simp only [Finsupp.sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of a two-point family. -/
lemma qf_two {X : Type*} (D : X → X → ℂ) (x y : X) (a b : ℂ) :
    (Finsupp.single x a + Finsupp.single y b).sum
        (fun i vi => (Finsupp.single x a + Finsupp.single y b).sum
          (fun j vj => star vi * D i j * vj))
      = star a * D x x * a + star a * D x y * b + star b * D y x * a + star b * D y y * b := by
  classical
  have key : ∀ (i : X) (c : ℂ),
      (Finsupp.single x a + Finsupp.single y b).sum (fun j vj => star c * D i j * vj)
        = star c * D i x * a + star c * D i y * b := by
    intro i c
    set h : X → ℂ → ℂ := fun j vj => star c * D i j * vj with hh
    have h0 : ∀ j : X, h j 0 = 0 := fun j => by simp [hh]
    have hA : ∀ (j : X) (p q : ℂ), h j (p + q) = h j p + h j q := by
      intro j p q; simp only [hh]; ring
    rw [Finsupp.sum_add_index (fun j _ => h0 j) (fun j _ => hA j),
      Finsupp.sum_single_index (h0 x), Finsupp.sum_single_index (h0 y)]
  calc (Finsupp.single x a + Finsupp.single y b).sum
          (fun i vi => (Finsupp.single x a + Finsupp.single y b).sum
            (fun j vj => star vi * D i j * vj))
      = (Finsupp.single x a + Finsupp.single y b).sum
          (fun i c => star c * D i x * a + star c * D i y * b) :=
        Finsupp.sum_congr fun i _ => key i _
    _ = (star a * D x x * a + star a * D x y * b) + (star b * D y x * a + star b * D y y * b) := by
        set h : X → ℂ → ℂ := fun i c => star c * D i x * a + star c * D i y * b with hh
        have h0 : ∀ i : X, h i 0 = 0 := fun i => by simp [hh]
        have hA : ∀ (i : X) (p q : ℂ), h i (p + q) = h i p + h i q := by
          intro i p q; simp only [hh, star_add]; ring
        rw [Finsupp.sum_add_index (fun i _ => h0 i) (fun i _ => hA i),
          Finsupp.sum_single_index (h0 x), Finsupp.sum_single_index (h0 y)]
    _ = star a * D x x * a + star a * D x y * b + star b * D y x * a + star b * D y y * b := by
        ring

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §7, p. 354
(PDF p. 18), unnumbered: on positive matrices, `≪` is a partial ordering. From
`K₁ ≪ K₂ ≪ K₃` it follows that `K₁ ≪ K₃`; if `K₁ ≪ K₂` and `K₂ ≪ K₁`, then `K₁ = K₂`. -/
theorem dominated_partialOrder {X : Type*} (K₁ K₂ K₃ : X → X → ℂ)
    (h₁ : (Matrix.of K₁).PosSemidef) (h₂ : (Matrix.of K₂).PosSemidef)
    (h₃ : (Matrix.of K₃).PosSemidef) :
    (AronszajnRK.Limits.KernelLE K₁ K₂ → AronszajnRK.Limits.KernelLE K₂ K₃ → AronszajnRK.Limits.KernelLE K₁ K₃) ∧
      (AronszajnRK.Limits.KernelLE K₁ K₂ → AronszajnRK.Limits.KernelLE K₂ K₁ → K₁ = K₂) := by
  classical
  have eK₁ := herm_entries K₁ h₁.1
  have eK₂ := herm_entries K₂ h₂.1
  have eK₃ := herm_entries K₃ h₃.1
  constructor
  · -- transitivity
    intro a12 a23
    obtain ⟨ha, fa⟩ := a12
    obtain ⟨hb, fb⟩ := a23
    simp only [Matrix.sub_apply, Matrix.of_apply] at fa fb
    refine ⟨herm_of_entries _ (fun i j => by
      show star (K₃ j i - K₁ j i) = K₃ i j - K₁ i j
      rw [star_sub, eK₃, eK₁]), ?_⟩
    intro v
    simp only [Matrix.sub_apply, Matrix.of_apply]
    have hsplit : (v.sum (fun i vi => v.sum (fun j vj => star vi * (K₃ i j - K₁ i j) * vj)))
        = (v.sum (fun i vi => v.sum (fun j vj => star vi * (K₃ i j - K₂ i j) * vj)))
          + (v.sum (fun i vi => v.sum (fun j vj => star vi * (K₂ i j - K₁ i j) * vj))) := by
      have hpts : ∀ i j, (K₃ i j - K₂ i j) + (K₂ i j - K₁ i j) = K₃ i j - K₁ i j :=
        fun i j => by ring
      rw [← qf_add (fun x y => K₃ x y - K₂ x y) (fun x y => K₂ x y - K₁ x y) v]
      refine Finsupp.sum_congr fun i _ => ?_
      refine Finsupp.sum_congr fun j _ => ?_
      rw [hpts i j]
    rw [hsplit]
    obtain ⟨r1, i1⟩ := Complex.nonneg_iff.mp (fb v)
    obtain ⟨r2, i2⟩ := Complex.nonneg_iff.mp (fa v)
    rw [Complex.nonneg_iff]
    constructor
    · rw [Complex.add_re]
      linarith
    · rw [Complex.add_im, ← i1, ← i2, add_zero]
  · -- antisymmetry
    intro a12 a21
    obtain ⟨ha, fa⟩ := a12
    obtain ⟨hb, fb⟩ := a21
    simp only [Matrix.sub_apply, Matrix.of_apply] at fa fb
    have eD := herm_entries _ ha
    -- every quadratic form of the difference vanishes
    have qzero : ∀ v : X →₀ ℂ,
        v.sum (fun i vi => v.sum (fun j vj => star vi * (K₂ i j - K₁ i j) * vj)) = 0 := by
      intro v
      obtain ⟨r1, i1⟩ := Complex.nonneg_iff.mp (fa v)
      have hcone : v.sum (fun i vi => v.sum (fun j vj => star vi * (K₁ i j - K₂ i j) * vj))
          = v.sum (fun i vi => v.sum (fun j vj => star vi * (-(K₂ i j - K₁ i j)) * vj)) :=
        Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => by ring
      have hneg := qf_neg (fun x y => K₂ x y - K₁ x y) v
      have hB : (0 : ℂ) ≤
          -v.sum (fun i vi => v.sum (fun j vj => star vi * (K₂ i j - K₁ i j) * vj)) := by
        rw [← hneg, ← hcone]
        exact fb v
      obtain ⟨r2, _⟩ := Complex.nonneg_iff.mp hB
      rw [Complex.neg_re] at r2
      refine Complex.ext ?_ ?_
      · rw [Complex.zero_re]
        have : (v.sum (fun i vi => v.sum (fun j vj => star vi * (K₂ i j - K₁ i j) * vj))).re = 0 := by
          linarith
        rw [← this]
      · rw [Complex.zero_im, ← i1]
    -- diagonal
    have diag : ∀ x, K₂ x x - K₁ x x = 0 := by
      intro x
      have := qzero (Finsupp.single x 1)
      simpa using this
    -- off-diagonal
    have offdiag : ∀ x y, K₂ x y - K₁ x y = 0 := by
      intro x y
      by_cases hxy : x = y
      · rw [hxy]; exact diag y
      · have hD' : (K₂ x y - K₁ x y) + (K₂ y x - K₁ y x) = 0 := by
          have h2 := qzero (Finsupp.single x 1 + Finsupp.single y 1)
          rw [qf_two (fun u v => K₂ u v - K₁ u v) x y 1 1, diag x, diag y] at h2
          simpa using h2
        have hE' : (K₂ x y - K₁ x y) * Complex.I + -(Complex.I * (K₂ y x - K₁ y x)) = 0 := by
          have h3 := qzero (Finsupp.single x 1 + Finsupp.single y Complex.I)
          rw [qf_two (fun u v => K₂ u v - K₁ u v) x y 1 Complex.I, diag x, diag y] at h3
          simpa using h3
        have h5 : (K₂ x y - K₁ x y) - (K₂ y x - K₁ y x) = 0 := by
          have hI : Complex.I * ((K₂ x y - K₁ x y) - (K₂ y x - K₁ y x)) = 0 := by
            rw [mul_sub, mul_comm Complex.I (K₂ x y - K₁ x y)]
            exact hE'
          exact (mul_eq_zero.mp hI).resolve_left Complex.I_ne_zero
        have hsum : ((K₂ x y - K₁ x y) + (K₂ y x - K₁ y x))
            + ((K₂ x y - K₁ x y) - (K₂ y x - K₁ y x)) = 0 := by
          rw [hD', h5, add_zero]
        have hzz : (K₂ x y - K₁ x y) + (K₂ x y - K₁ x y) = 0 := by
          rw [← hsum]
          ring
        have hz2 : (K₂ x y - K₁ x y) * 2 = 0 := by
          rw [mul_two]
          exact hzz
        exact (mul_eq_zero.mp hz2).resolve_right two_ne_zero
    funext x y
    exact (sub_eq_zero.mp (offdiag x y)).symm

end AronszajnRK.Inclusion

/-- Solution entry point. -/
theorem solution {X : Type*} (K₁ K₂ K₃ : X → X → ℂ)
    (h₁ : (Matrix.of K₁).PosSemidef) (h₂ : (Matrix.of K₂).PosSemidef)
    (h₃ : (Matrix.of K₃).PosSemidef) :
    (AronszajnRK.Limits.KernelLE K₁ K₂ → AronszajnRK.Limits.KernelLE K₂ K₃ → AronszajnRK.Limits.KernelLE K₁ K₃) ∧
      (AronszajnRK.Limits.KernelLE K₁ K₂ → AronszajnRK.Limits.KernelLE K₂ K₁ → K₁ = K₂) :=
  AronszajnRK.Inclusion.dominated_partialOrder K₁ K₂ K₃ h₁ h₂ h₃
