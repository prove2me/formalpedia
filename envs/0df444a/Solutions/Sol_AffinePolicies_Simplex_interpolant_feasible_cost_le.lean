-- Prove2me | solution 1 for AffinePolicies.Simplex.interpolant_feasible_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:07:02.407133+00:00
-- url     : https://prove2.me/submissions/3dea58cf-5305-4fc1-b455-922717a8a184

import Mathlib
import Definitions.Def_AffinePolicies_Simplex_Setting

set_option autoImplicit false

open AffinePolicies.Simplex Matrix in
theorem AP5149_Q_isUnit {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) : IsUnit (Qmat v) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  rw [affineIndependent_iff_linearIndependent_vsub ℝ v (Fin.last m)] at hv
  have hinj : Function.Injective
      (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x // x ≠ Fin.last m})) := by
    intro a b h
    simpa using congrArg Subtype.val h
  have e : (Qmat v).col = (fun i : {x // x ≠ Fin.last m} => (v i -ᵥ v (Fin.last m) : Fin m → ℝ)) ∘
      (fun j : Fin m => (⟨Fin.castSucc j, Fin.castSucc_ne_last j⟩ : {x // x ≠ Fin.last m})) := by
    funext j i
    simp [Qmat, Matrix.col]
  rw [e]
  exact hv.comp _ hinj

open AffinePolicies.Simplex Matrix in
theorem AP5149_main {m n₂ : ℕ} (v : Fin (m + 1) → Fin m → ℝ)
    (hv : AffineIndependent ℝ v) (g : (Fin m → ℝ) → Fin n₂ → ℝ)
    (α : Fin (m + 1) → ℝ) (hα1 : ∑ j, α j = 1) :
    interpolant v g (∑ j, α j • v j) = ∑ j, α j • g (v j) := by
  set β : Fin m → ℝ := fun j => α (Fin.castSucc j) with hβ
  have hlast : α (Fin.last m) = 1 - ∑ j, β j := by
    rw [← hα1, Fin.sum_univ_castSucc]; ring
  have hQ : ∑ j, α j • v j - v (Fin.last m) = Qmat v *ᵥ β := by
    funext i
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Qmat, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hβ, Finset.sum_sub_distrib, sub_mul, one_mul, Finset.sum_mul, mul_comm (α _) _]
    ring
  have hdet : IsUnit (Qmat v).det := (Matrix.isUnit_iff_isUnit_det _).1 (AP5149_Q_isUnit v hv)
  unfold interpolant
  rw [hQ, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct, Ymat, Matrix.of_apply]
  rw [Fin.sum_univ_castSucc, hlast]
  simp only [hβ, Finset.sum_sub_distrib, sub_mul, one_mul, Finset.sum_mul, mul_comm (α _) _]
  ring


theorem AP5149_hull_rep {m : ℕ} (v : Fin (m + 1) → Fin m → ℝ) (b : Fin m → ℝ)
    (hb : b ∈ convexHull ℝ (Set.range v)) :
    ∃ α : Fin (m + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧ b = ∑ k, α k • v k := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hb
  obtain ⟨s, w, hw0, hw1, rfl⟩ := hb
  refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ s
    · simp [hk, hw0 k hk]
    · simp [hk]
  · rw [Finset.sum_ite_mem, Finset.univ_inter, hw1]
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

open AffinePolicies.Simplex Matrix in
theorem AP5149_core {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hfs : Feasible A B (simplexSet v) xs ys) :
    Feasible A B (simplexSet v) xs (interpolant v ys) ∧
      ∀ t : ℝ, CostLE c d (simplexSet v) xs ys t →
        CostLE c d (simplexSet v) xs (interpolant v ys) t := by
  obtain ⟨hx0, hfs⟩ := hfs
  have hvert : ∀ k, v k ∈ simplexSet v := fun k =>
    subset_convexHull ℝ (Set.range v) (Set.mem_range_self k)
  have key : ∀ b ∈ simplexSet v, ∃ α : Fin (m + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
      b = ∑ k, α k • v k ∧ interpolant v ys b = ∑ k, α k • ys (v k) := by
    intro b hb
    obtain ⟨α, h0, h1, rfl⟩ := AP5149_hull_rep v b hb
    exact ⟨α, h0, h1, rfl, AP5149_main v hv ys α h1⟩
  refine ⟨⟨hx0, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨α, h0, h1, hbα, hI⟩ := key b hb
    rw [hI]
    refine ⟨Finset.sum_nonneg fun k _ => smul_nonneg (h0 k) (hfs _ (hvert k)).1, ?_⟩
    have hAx : A *ᵥ xs = ∑ k, α k • (A *ᵥ xs) := by
      rw [← Finset.sum_smul, h1, one_smul]
    rw [Matrix.mulVec_sum, hAx, ← Finset.sum_add_distrib, hbα]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Matrix.mulVec_smul, ← smul_add]
    exact smul_le_smul_of_nonneg_left (hfs _ (hvert k)).2 (h0 k)
  · intro t ht b hb
    obtain ⟨α, h0, h1, hbα, hI⟩ := key b hb
    rw [hI, dotProduct_sum]
    have hcx : c ⬝ᵥ xs = ∑ k, α k * (c ⬝ᵥ xs) := by
      rw [← Finset.sum_mul, h1, one_mul]
    have ht' : t = ∑ k, α k * t := by rw [← Finset.sum_mul, h1, one_mul]
    rw [hcx, ht', ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [dotProduct_smul, smul_eq_mul, ← mul_add]
    exact mul_le_mul_of_nonneg_left (ht _ (hvert k)) (h0 k)

open AffinePolicies.Simplex in
theorem solution {m n₁ n₂ : ℕ} (A : Matrix (Fin m) (Fin n₁) ℝ)
    (B : Matrix (Fin m) (Fin n₂) ℝ) (c : Fin n₁ → ℝ) (d : Fin n₂ → ℝ)
    (v : Fin (m + 1) → Fin m → ℝ) (hv : AffineIndependent ℝ v)
    (xs : Fin n₁ → ℝ) (ys : (Fin m → ℝ) → Fin n₂ → ℝ)
    (hfs : Feasible A B (simplexSet v) xs ys) :
    Feasible A B (simplexSet v) xs (interpolant v ys) ∧
      ∀ t : ℝ, CostLE c d (simplexSet v) xs ys t →
        CostLE c d (simplexSet v) xs (interpolant v ys) t := by
  exact AP5149_core A B c d v hv xs ys hfs
