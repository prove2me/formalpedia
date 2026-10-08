-- Prove2me | solution 1 for AdaGrad.Full.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:33:04.143685+00:00
-- url     : https://prove2.me/submissions/96c98c2d-2c0c-463d-be95-5585278edeb3

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

set_option autoImplicit false

namespace AdaGrad.Full.L16Aux

open AdaGrad.Full

lemma quad_expand {d : ℕ} (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
    (hsym : L.IsSymmetric) (p q : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    ⟪p + s • q, L (p + s • q)⟫_ℝ = ⟪p, L p⟫_ℝ + 2 * s * ⟪q, L p⟫_ℝ + s ^ 2 * ⟪q, L q⟫_ℝ := by
  have h1 : ⟪p, L q⟫_ℝ = ⟪q, L p⟫_ℝ := by
    rw [← hsym p q, real_inner_comm]
  simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, h1]
  ring

lemma mul_pinv_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    A * pinv A * A = A := by
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f => hfin.continuousOn f
  have e1 : A * pinv A = cfc (fun x : ℝ => x * x⁻¹) A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x⁻¹) A (hc _) (hc _), cfc_id' ℝ A]
    rfl
  have e2 : cfc (fun x : ℝ => x * x⁻¹) A * A = cfc (fun x : ℝ => (x * x⁻¹) * x) A := by
    rw [cfc_mul (fun x : ℝ => x * x⁻¹) (fun x : ℝ => x) A (hc _) (hc _), cfc_id' ℝ A]
  have e3 : (fun x : ℝ => (x * x⁻¹) * x) = fun x => x := by
    funext x
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · field_simp
  rw [e1, e2, e3, cfc_id' ℝ A]

lemma toEuc_comp {d : ℕ} (M N : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin N v) = Matrix.toEuclideanLin (M * N) v := by
  show WithLp.toLp 2 (Matrix.mulVec M (Matrix.mulVec N (WithLp.ofLp v))) =
    WithLp.toLp 2 (Matrix.mulVec (M * N) (WithLp.ofLp v))
  rw [Matrix.mulVec_mulVec]

end AdaGrad.Full.L16Aux

open AdaGrad.Full in
theorem solution {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (hXcl : IsClosed X)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (hrun : IsQuadMirrorDescentRun η X ϕ f H x g T) (t : ℕ) (ht : t ∈ Finset.Icc 1 T)
    (hH : (H t).PosSemidef) (hrange : g t ∈ LinearMap.range (Matrix.toEuclideanLin (H t)))
    (xstar : EuclideanSpace ℝ (Fin d)) (hstar : xstar ∈ X) :
    η * (f t (x t) - f t xstar) + η * (ϕ (x (t + 1)) - ϕ xstar) ≤
      bregman (H t) xstar (x t) - bregman (H t) xstar (x (t + 1))
        + η ^ 2 / 2 * dualNormSq (H t) (g t) := by
  obtain ⟨hsub, hmem, hmin⟩ := hrun t ht
  obtain ⟨w, hw⟩ := hrange
  set A := H t with hA
  set y := x t with hy
  set z := x (t + 1) with hz
  set L := Matrix.toEuclideanLin A with hL
  have hsym : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH.isHermitian
  have hpos : ∀ v, 0 ≤ ⟪v, L v⟫_ℝ := fun v =>
    (Matrix.isPositive_toEuclideanLin_iff.mpr hH).inner_nonneg_right v
  set u := z - y with hu
  set v := xstar - z with hv
  -- scalar names
  set a := ⟪u, L u⟫_ℝ with ha
  set b := ⟪v, L u⟫_ℝ with hb
  set c := ⟪v, L v⟫_ℝ with hc
  have hc0 : 0 ≤ c := hpos v
  -- bregman values
  have hB1 : bregman A xstar y = (1 / 2) * (a + 2 * b + c) := by
    have : xstar - y = u + (1 : ℝ) • v := by rw [one_smul, hu, hv]; abel
    show (1 / 2) * ⟪xstar - y, L (xstar - y)⟫_ℝ = _
    rw [this, L16Aux.quad_expand L hsym]; ring
  have hB2 : bregman A xstar z = (1 / 2) * c := rfl
  have hBz : bregman A z y = (1 / 2) * a := rfl
  -- optimality condition
  have hK : 0 ≤ η * ⟪g t, v⟫_ℝ + η * (ϕ xstar - ϕ z) + b := by
    set K := η * ⟪g t, v⟫_ℝ + η * (ϕ xstar - ϕ z) + b with hKdef
    have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ K + s * c / 2 := by
      intro s hs0 hs1
      have hp : z + s • (xstar - z) ∈ X :=
        hXc.add_smul_sub_mem hmem hstar ⟨hs0.le, hs1⟩
      have hle := (isMinOn_iff.mp hmin) _ hp
      try dsimp only at hle
      have hϕs : ϕ (z + s • v) ≤ (1 - s) * ϕ z + s * ϕ xstar := by
        have h := hϕ.2 (Set.mem_univ z) (Set.mem_univ xstar) (by linarith : (0:ℝ) ≤ 1 - s)
          hs0.le (by ring)
        have e : (1 - s) • z + s • xstar = z + s • v := by
          rw [hv, smul_sub, sub_smul, one_smul]; abel
        rw [e] at h
        simpa [smul_eq_mul] using h
      have hBp : bregman A (z + s • v) y = (1 / 2) * (a + 2 * s * b + s ^ 2 * c) := by
        have : z + s • v - y = u + s • v := by rw [hu]; abel
        show (1 / 2) * ⟪z + s • v - y, L (z + s • v - y)⟫_ℝ = _
        rw [this, L16Aux.quad_expand L hsym]
      have hgp : ⟪g t, z + s • v⟫_ℝ = ⟪g t, z⟫_ℝ + s * ⟪g t, v⟫_ℝ := by
        rw [inner_add_right, real_inner_smul_right]
      rw [← hv] at hle
      rw [hBp, hgp, hBz] at hle
      have h3 : η * ϕ (z + s • v) ≤ η * ((1 - s) * ϕ z + s * ϕ xstar) :=
        mul_le_mul_of_nonneg_left hϕs hη.le
      have h4 : 0 ≤ s * (K + s * c / 2) := by
        rw [hKdef]; nlinarith
      by_contra hneg
      push_neg at hneg
      have : s * (K + s * c / 2) < 0 := mul_neg_of_pos_of_neg hs0 hneg
      linarith
    by_contra hneg
    push_neg at hneg
    set s := min 1 (-K / (c + 1)) with hsdef
    have hc1 : 0 < c + 1 := by linarith
    have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hc1)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ -K / (c + 1) := min_le_right _ _
    have h5 := key s hs0 hs1
    have h6 : s * (c + 1) ≤ -K := (le_div_iff₀ hc1).mp hs2
    nlinarith
  -- subgradient inequality
  have hsg := hsub xstar
  have hxs : xstar - y = v + u := by rw [hu, hv]; abel
  rw [hxs, inner_add_right] at hsg
  -- Fenchel-Young type inequality via the range condition
  set m := ⟪w, L w⟫_ℝ with hm
  set k := ⟪w, L u⟫_ℝ with hk
  have hgu : ⟪g t, u⟫_ℝ = k := by
    rw [← hw, hk]; exact hsym w u
  have hdual : dualNormSq A (g t) = m := by
    show ⟪g t, Matrix.toEuclideanLin (pinv A) (g t)⟫_ℝ = _
    rw [← hw]
    show ⟪L w, Matrix.toEuclideanLin (pinv A) (L w)⟫_ℝ = _
    rw [hsym w, hL, L16Aux.toEuc_comp, L16Aux.toEuc_comp, L16Aux.mul_pinv_mul A hH.isHermitian]
  have hFY : 0 ≤ η ^ 2 * m + 2 * η * k + a := by
    have h := hpos (u + η • w)
    rw [L16Aux.quad_expand L hsym] at h
    have hwu : ⟪w, L u⟫_ℝ = k := rfl
    rw [hwu] at h
    nlinarith
  rw [hB1, hB2, hdual]
  rw [hgu] at hsg
  have h7 : η * (f t y - f t xstar) ≤ -(η * (⟪g t, v⟫_ℝ + k)) := by
    have := mul_le_mul_of_nonneg_left (show ⟪g t, v⟫_ℝ + k ≤ f t xstar - f t y by linarith) hη.le
    linarith
  nlinarith
