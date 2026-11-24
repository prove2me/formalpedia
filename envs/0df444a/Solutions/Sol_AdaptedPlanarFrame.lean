-- Prove2me | solution 1 for AdaptedPlanarFrame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T14:26:43.183795+00:00
-- url     : https://prove2.me/submissions/d2026ca8-fe7c-4301-9d08-a2008e3f5537

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_AdaptedPlanarFrame

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {e v : EuclideanSpace ℝ (Fin n)}
    (he : ‖e‖ = 1) (hv : ‖v‖ = 1) (hev : inner ℝ e v = (0 : ℝ)) (th : ℝ) :
    ∃ (i0 i1 : Fin n) (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))),
      i0 ≠ i1
        ∧ b i0 = (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))
        ∧ b i1 = ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n))
        ∧ ∀ i : Fin n, i ≠ i0 → i ≠ i1 →
            (inner ℝ e (b i) : ℝ) = 0 ∧ (inner ℝ v (b i) : ℝ) = 0 := by
  classical
  have hnorm1 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 = 1 → ‖x‖ = 1 := by
    intro x hsq
    have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hf : (‖x‖ - 1) * (‖x‖ + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hf with h | h
    · linarith
    · linarith
  have hcssq : Real.cos th ^ 2 + Real.sin th ^ 2 = 1 := by
    rw [add_comm]
    exact Real.sin_sq_add_cos_sq _
  have hee : (inner ℝ e e : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  have hvv : (inner ℝ v v : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  have hve : (inner ℝ v e : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hev
  -- the rotated planar frame is orthonormal
  have hx0n : ‖(Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hsq : ‖(Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hee, hvv, hev, hve]
      linear_combination hcssq
    exact hnorm1 _ hsq
  have hetn : ‖((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have hsq : ‖((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, neg_smul,
        real_inner_smul_left, real_inner_smul_right, hee, hvv, hev, hve]
      linear_combination hcssq
    exact hnorm1 _ hsq
  have hx0et : (inner ℝ (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))
      ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
    simp only [inner_add_left, inner_add_right, inner_neg_right, neg_smul,
      real_inner_smul_left, real_inner_smul_right, hee, hvv, hev, hve]
    ring
  have hetx0 : (inner ℝ ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n))
      (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
    rw [real_inner_comm]
    exact hx0et
  -- two distinct indices to carry the planar frame
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, (i : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨i1, hi1⟩ : ∃ i : Fin n, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    rw [h, hi1] at hi0
    omega
  have hon : Orthonormal ℝ (Set.domRestrict ({i0, i1} : Set (Fin n))
      (fun i : Fin n => if i = i0 then
          (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))
        else ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n)))) := by
    constructor
    · rintro ⟨i, hi⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · simpa [Set.domRestrict] using hx0n
      · simpa [Set.domRestrict, Ne.symm hi01] using hetn
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hne : i ≠ j := by
        intro h
        exact hij (by subst h; rfl)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact absurd rfl hne
      · simpa [Set.domRestrict, Ne.symm hi01] using hx0et
      · simpa [Set.domRestrict, Ne.symm hi01] using hetx0
      · exact absurd rfl hne
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp) hon
  have hb0 : b i0 = (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n)) := by
    have h := hb i0 (by simp)
    simp at h
    exact h
  have hb1 : b i1 = ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n)) := by
    have h := hb i1 (by simp)
    rw [if_neg (Ne.symm hi01)] at h
    exact h
  -- the decompositions of `e` and `v` in the planar frame
  have hdecE : (e : EuclideanSpace ℝ (Fin n))
      = Real.cos th • (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))
        + (-Real.sin th) • ((-Real.sin th • e + Real.cos th • v)
          : EuclideanSpace ℝ (Fin n)) := by
    match_scalars
    all_goals first
      | ring1
      | linarith [Real.sin_sq_add_cos_sq th]
  have hdecV : (v : EuclideanSpace ℝ (Fin n))
      = Real.sin th • (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n))
        + Real.cos th • ((-Real.sin th • e + Real.cos th • v)
          : EuclideanSpace ℝ (Fin n)) := by
    match_scalars
    all_goals first
      | ring1
      | linarith [Real.sin_sq_add_cos_sq th]
  refine ⟨i0, i1, b, hi01, hb0, hb1, ?_⟩
  intro i hne0 hne1
  have hib0 : (inner ℝ (b i)
      (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
    rw [← hb0]
    exact b.orthonormal.2 hne0
  have hib1 : (inner ℝ (b i)
      ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n)) : ℝ) = 0 := by
    rw [← hb1]
    exact b.orthonormal.2 hne1
  refine ⟨?_, ?_⟩
  · rw [real_inner_comm]
    have hsplit : (inner ℝ (b i) e : ℝ)
        = Real.cos th * (inner ℝ (b i)
            (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n)) : ℝ)
          + (-Real.sin th) * (inner ℝ (b i)
            ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n)) : ℝ) := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, ← hdecE]
    rw [hsplit, hib0, hib1]
    ring
  · rw [real_inner_comm]
    have hsplit : (inner ℝ (b i) v : ℝ)
        = Real.sin th * (inner ℝ (b i)
            (Real.cos th • e + Real.sin th • v : EuclideanSpace ℝ (Fin n)) : ℝ)
          + Real.cos th * (inner ℝ (b i)
            ((-Real.sin th • e + Real.cos th • v) : EuclideanSpace ℝ (Fin n)) : ℝ) := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, ← hdecV]
    rw [hsplit, hib0, hib1]
    ring
