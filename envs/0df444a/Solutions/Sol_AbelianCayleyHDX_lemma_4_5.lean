-- Prove2me | solution 1 for AbelianCayleyHDX.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:16:31.130696+00:00
-- url     : https://prove2.me/submissions/b98668ac-35eb-4155-8083-83966af06720

import Mathlib
import Definitions.Def_AbelianCayleyHDX_affineSpace

namespace AbelianCayleyHDX.L45

open Matrix

variable {F : Type*} [Field F]

/-- The determinant of a rank-one perturbation is affine in the scalar. -/
lemma det_rank_one_affine {n : Type*} [Fintype n] [DecidableEq n] (C : Matrix n n F)
    (u v : n → F) : ∃ A B : F, ∀ α : F, (C + α • vecMulVec u v).det = A + B * α := by
  by_cases hu : u = 0
  · exact ⟨C.det, 0, fun α => by simp [hu]⟩
  obtain ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  let w : n → F := fun i => if i = i0 then 0 else -(u i / u i0)
  let E : Matrix n n F := 1 + vecMulVec w (Pi.single i0 1)
  have hE : E.det = 1 := by
    simp only [E]
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, single_dotProduct]
    simp [w]
  have hEu : E *ᵥ u = Pi.single i0 (u i0) := by
    funext i
    have : (vecMulVec w (Pi.single i0 1) *ᵥ u) i = w i * u i0 := by
      simp [mulVec, dotProduct, vecMulVec_apply, Pi.single_apply]
    simp only [E, add_mulVec, one_mulVec, Pi.add_apply, this]
    by_cases hi : i = i0
    · subst hi; simp [w]
    · simp only [w, if_neg hi, Pi.single_apply, hi, if_false]
      field_simp; ring
  have hM : ∀ α : F, E * (C + α • vecMulVec u v) =
      (E * C).updateRow i0 ((E * C) i0 + (α * u i0) • v) := by
    intro α
    rw [Matrix.mul_add, Matrix.mul_smul, mul_vecMulVec, hEu]
    ext i j
    by_cases hi : i = i0
    · subst hi
      simp [updateRow_self, vecMulVec_apply, mul_comm, mul_left_comm]
    · simp [updateRow_ne hi, vecMulVec_apply, Pi.single_apply, hi]
  refine ⟨(E * C).det, u i0 * ((E * C).updateRow i0 v).det, fun α => ?_⟩
  have h1 : (E * (C + α • vecMulVec u v)).det = (C + α • vecMulVec u v).det := by
    rw [det_mul, hE, one_mul]
  rw [← h1, hM, det_updateRow_add, det_updateRow_smul, updateRow_eq_self]
  ring

end AbelianCayleyHDX.L45

open AbelianCayleyHDX AbelianCayleyHDX.L45 in
theorem solution {F : Type*} [Field F] {t k m : ℕ} (L : Fin k → Fin m → Module.Dual F (Fin t → F)) :
    (∀ (e : Fin t → F) (a : Fin k → F) (b : Fin m → F), (∀ i j, L i j e = a i * b j) →
      (∀ (x : Fin t → F) (α : F), Matrix.of (fun i j => L i j (x + α • e)) =
        Matrix.of (fun i j => L i j x) + α • Matrix.vecMulVec a b) ∧
      ∀ (J : Finset (Fin m)) (hJ : J.card = k),
        IsAffineIn (fun x => (Matrix.of fun i l => L i (J.orderEmbOfFin hJ l) x).det) e) ∧
    ∀ D : Finset (PG t F),
      (∀ d ∈ D, ∃ (e : Fin t → F) (he : e ≠ 0) (a : Fin k → F) (b : Fin m → F),
        Projectivization.mk F e he = d ∧ ∀ i j, L i j e = a i * b j) →
      ∀ (J : Finset (Fin m)) (hJ : J.card = k),
        (fun x => (Matrix.of fun i l => L i (J.orderEmbOfFin hJ l) x).det) ∈ affineSpace D := by
  have part : ∀ (e : Fin t → F) (a : Fin k → F) (b : Fin m → F), (∀ i j, L i j e = a i * b j) →
      (∀ (x : Fin t → F) (α : F), Matrix.of (fun i j => L i j (x + α • e)) =
        Matrix.of (fun i j => L i j x) + α • Matrix.vecMulVec a b) ∧
      ∀ (J : Finset (Fin m)) (hJ : J.card = k),
        IsAffineIn (fun x => (Matrix.of fun i l => L i (J.orderEmbOfFin hJ l) x).det) e := by
    intro e a b hL
    have h1 : ∀ (x : Fin t → F) (α : F), Matrix.of (fun i j => L i j (x + α • e)) =
        Matrix.of (fun i j => L i j x) + α • Matrix.vecMulVec a b := by
      intro x α
      ext i j
      simp [map_add, map_smul, hL, Matrix.vecMulVec_apply]
    refine ⟨h1, fun J hJ x => ?_⟩
    obtain ⟨A, B, hAB⟩ := det_rank_one_affine
      (Matrix.of fun i l => L i (J.orderEmbOfFin hJ l) x) a (fun l => b (J.orderEmbOfFin hJ l))
    refine ⟨A, B, fun α => ?_⟩
    rw [← hAB α]
    show Matrix.det _ = Matrix.det _
    congr 1
    ext i l
    have := congrFun (congrFun (h1 x α) i) (J.orderEmbOfFin hJ l)
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply] at this ⊢
    rw [this]
    simp [Matrix.vecMulVec_apply]
  refine ⟨part, fun D hD J hJ d hd => ?_⟩
  obtain ⟨e, he, a, b, hed, hL⟩ := hD d hd
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep F e he
  rw [hed] at hc
  have hL' : ∀ i j, L i j d.rep = ((c : F) * a i) * b j := by
    intro i j
    rw [← hc, Units.smul_def, map_smul, hL, smul_eq_mul]; ring
  exact (part d.rep (fun i => (c : F) * a i) b hL').2 J hJ
