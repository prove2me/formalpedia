-- Prove2me | solution 1 for AlgebraicCurve.det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0f80fd45-1207-575d-8e21-ccfa54cb3d9e

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_mul
import Theorems.Thm_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (hpat : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational) (hord : ∀ i, (P i).ord (t i) = 1)
    (u : Fin M → F) (hu : ∀ i j, u j ∈ (P i).toValuationSubring)
    (c : Place K F → F) (hc : ∀ i, c (P i) ∈ (P i).toValuationSubring) :
    (Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (u j * c (P i))).det
      = (∏ i, (P i).evalAt (c (P i))) * (jetMatrix P t e u).det := by
  classical
  obtain ⟨h1, h2, h3⟩ := hpat

  set L : Matrix (Fin M) (Fin M) K := Matrix.of fun i i' =>
    if P i' = P i ∧ e i' ≤ e i then (P i).taylorCoeff (t i) (e i - e i') (c (P i)) else 0 with hL
  have hmul : L * jetMatrix P t e u
      = Matrix.of fun i j => (P i).taylorCoeff (t i) (e i) (u j * c (P i)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply,
      taylorCoeff_mul (P i) (hrat i) (hord i) (hu i j) (hc i) (e i)]
    simp only [hL, Matrix.of_apply, jetMatrix_apply, ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i' _ => (e i', e i - e i')) ?_ ?_ ?_ ?_
    · intro i' hi'
      obtain ⟨-, hle⟩ := (Finset.mem_filter.mp hi').2
      simp only [Finset.HasAntidiagonal.mem_antidiagonal]; omega
    · intro a ha b hb hab
      obtain ⟨hPa, -⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨hPb, -⟩ := (Finset.mem_filter.mp hb).2
      exact h2 a b (hPa.trans hPb.symm) (congrArg Prod.fst hab)
    · intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      have hq : x.1 < jetMult P (P i) := by have := h3 i; omega
      obtain ⟨i', hP, he⟩ := IsConfluentPattern.exists_eq_of_lt_jetMult ⟨h1, h2, h3⟩ i hq
      refine ⟨i', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP, by omega⟩, ?_⟩
      ext
      · exact he
      · show e i - e i' = x.2; omega
    · intro i' hi'
      obtain ⟨hP, -⟩ := (Finset.mem_filter.mp hi').2
      rw [hP, h1 i' i hP, mul_comm]

  have hBT : L.BlockTriangular (⇑OrderDual.toDual ∘ e) := by
    intro i j hlt
    change OrderDual.toDual (e j) < OrderDual.toDual (e i) at hlt
    rw [OrderDual.toDual_lt_toDual] at hlt
    simp only [hL, Matrix.of_apply]
    rw [if_neg]
    rintro ⟨-, hle⟩; omega
  have hblock : ∀ k, (L.toSquareBlock (⇑OrderDual.toDual ∘ e) k).det
      = ∏ a : {a // (⇑OrderDual.toDual ∘ e) a = k}, (P a.1).evalAt (c (P a.1)) := by
    intro k
    have hdiag : L.toSquareBlock (⇑OrderDual.toDual ∘ e) k
        = Matrix.diagonal fun a => (P a.1).evalAt (c (P a.1)) := by
      ext ⟨p, hp⟩ ⟨q, hq⟩
      rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.diagonal_apply]
      simp only [hL, Matrix.of_apply]
      by_cases hpq : p = q
      · subst hpq
        rw [if_pos ⟨rfl, le_rfl⟩, if_pos rfl, Nat.sub_self, taylorCoeff_zero]
      · have hne : (⟨p, hp⟩ : {a // (⇑OrderDual.toDual ∘ e) a = k}) ≠ ⟨q, hq⟩ :=
          fun h => hpq (congrArg Subtype.val h)
        rw [if_neg hne, if_neg]
        rintro ⟨hP, -⟩
        have hee : e p = e q := by
          have := hp.trans hq.symm
          simpa using this
        exact hpq (h2 p q hP.symm hee)
    rw [hdiag, Matrix.det_diagonal]
  have hdet : L.det = ∏ i, (P i).evalAt (c (P i)) := by
    rw [Matrix.BlockTriangular.det hBT]
    simp_rw [hblock]
    have hsub : ∀ k, ∏ a : {a // (⇑OrderDual.toDual ∘ e) a = k}, (P a.1).evalAt (c (P a.1))
        = ∏ a ∈ Finset.univ.filter (fun a => (⇑OrderDual.toDual ∘ e) a = k), (P a).evalAt (c (P a)) :=
      fun k => (Finset.prod_subtype (Finset.univ.filter fun a => (⇑OrderDual.toDual ∘ e) a = k)
        (p := fun a => (⇑OrderDual.toDual ∘ e) a = k) (fun x => by simp)
        (fun a => (P a).evalAt (c (P a)))).symm
    simp_rw [hsub]
    exact Finset.prod_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i)) _
  rw [← hmul, Matrix.det_mul, hdet]

end S_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix
end P2MW
export P2MW.S_AlgebraicCurve_det_taylorCoeff_mul_eq_prod_evalAt_mul_det_jetMatrix (solution)
