-- Prove2me | solution 1 for AlgebraicFPT.HittingSet.coordinate_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:11:52.590793+00:00
-- url     : https://prove2.me/submissions/0a0a97b0-ecbb-47e7-9ab1-a70d235080d5

import Definitions.Def_AlgebraicFPT_HittingSet_Model
import Definitions.Def_HSElemKernel_HSInstance

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial
namespace AlgebraicFPT.HittingSet
noncomputable section

variable {n : ℕ}

lemma zeroSet_eq_zeroLocus (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    RSCapacity.zeroSet (I : Set (MvPolynomial (Fin n) ℂ)) = zeroLocus ℂ I := by
  ext x
  change (∀ f ∈ I, eval x f = 0) ↔ _
  simp only [mem_zeroLocus_iff, aeval_eq_eval]

def restrictPoly (C : Finset (Fin n)) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial {i : Fin n // i ∉ C} ℂ :=
  aeval (fun i => if h : i ∈ C then 0 else X ⟨i, h⟩)

def extendPoint (C : Finset (Fin n)) (x : {i : Fin n // i ∉ C} → ℂ) : Fin n → ℂ :=
  fun i => if h : i ∈ C then 0 else x ⟨i, h⟩

lemma extendPoint_mem (C : Finset (Fin n)) (x : {i : Fin n // i ∉ C} → ℂ) :
    extendPoint C x ∈ coordinateSubspace C := by
  intro i hi
  simp [extendPoint, hi]

lemma eval_restrict (C : Finset (Fin n)) (x : {i : Fin n // i ∉ C} → ℂ)
    (p : MvPolynomial (Fin n) ℂ) :
    eval x (restrictPoly C p) = eval (extendPoint C x) p := by
  have h : (aeval x).comp (restrictPoly C) = aeval (extendPoint C x) := by
    ext i
    by_cases hi : i ∈ C <;> simp [restrictPoly, extendPoint, hi]
  exact AlgHom.congr_fun h p

lemma restrict_surjective (C : Finset (Fin n)) : Function.Surjective (restrictPoly C) := by
  intro p
  refine ⟨rename Subtype.val p, ?_⟩
  have h : (restrictPoly C).comp (rename Subtype.val) = AlgHom.id ℂ _ := by
    ext i
    simp [restrictPoly, i.property]
  exact AlgHom.congr_fun h p

lemma ker_restrict (C : Finset (Fin n)) :
    RingHom.ker (restrictPoly C).toRingHom = vanishingIdeal ℂ (coordinateSubspace C) := by
  ext p
  change restrictPoly C p = 0 ↔ ∀ x ∈ coordinateSubspace C, aeval x p = 0
  constructor
  · intro hp x hx
    have he : extendPoint C (fun i => x i) = x := by
      funext i
      by_cases hi : i ∈ C
      · simp [extendPoint, hi, hx i hi]
      · simp [extendPoint, hi]
    have := eval_restrict C (fun i => x i) p
    simpa [hp, he, aeval_eq_eval] using this.symm
  · intro hp
    apply MvPolynomial.funext
    intro x
    rw [eval_restrict, map_zero]
    exact hp _ (extendPoint_mem C x)

lemma coord_prime (C : Finset (Fin n)) :
    (vanishingIdeal ℂ (coordinateSubspace C)).IsPrime := by
  rw [← ker_restrict]
  exact RingHom.ker_isPrime _

lemma coord_codim (C : Finset (Fin n)) : HasCodim (coordinateSubspace C) C.card := by
  let e := RingHom.quotientKerEquivOfSurjective (restrict_surjective C)
  have he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ vanishingIdeal ℂ (coordinateSubspace C)) =
      ringKrullDim (MvPolynomial {i : Fin n // i ∉ C} ℂ) := by
    rw [← ker_restrict]
    exact ringKrullDim_eq_of_ringEquiv e
  refine ⟨n - C.card, ?_, Nat.sub_add_cancel (by simpa using Finset.card_le_univ C)⟩
  change ringKrullDim _ = _
  rw [he, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp only [zero_add, Nat.card_eq_fintype_card]
  congr 2
  simpa using Fintype.card_subtype_compl (fun i : Fin n => i ∈ C)

lemma coord_subset_iff (C D : Finset (Fin n)) :
    coordinateSubspace C ⊆ coordinateSubspace D ↔ D ⊆ C := by
  classical
  constructor
  · intro h i hi
    by_contra hc
    have hx : (fun j : Fin n => if j ∈ C then (0 : ℂ) else 1) ∈ coordinateSubspace C := by
      intro j hj
      simp [hj]
    have := h hx i hi
    simp [hc] at this
  · intro h x hx i hi
    exact hx i (h hi)

lemma coord_injective : Function.Injective (@coordinateSubspace n) := by
  intro C D h
  exact Finset.Subset.antisymm ((coord_subset_iff D C).mp h.ge) ((coord_subset_iff C D).mp h.le)

lemma edge_mem (E : Finset (Finset (Fin n))) (x : Fin n → ℂ) :
    x ∈ edgeVariety E ↔ ∀ e ∈ E, ∃ i ∈ e, x i = 0 := by
  rw [edgeVariety, zeroSet_eq_zeroLocus, edgeIdeal, zeroLocus_span]
  simp [edgeMonomial, aeval_eq_eval, Finset.prod_eq_zero_iff]

lemma coord_subset_edge (E : Finset (Finset (Fin n))) (C : Finset (Fin n))
    (hC : IsHitting E C) : coordinateSubspace C ⊆ edgeVariety E := by
  intro x hx
  rw [edge_mem]
  intro e he
  obtain ⟨i, hi⟩ := hC e he
  exact ⟨i, (Finset.mem_inter.mp hi).2, hx i (Finset.mem_inter.mp hi).1⟩

lemma prime_has_hitting (E : Finset (Finset (Fin n))) (p : Ideal (MvPolynomial (Fin n) ℂ))
    (hp : p.IsPrime) (hEp : vanishingIdeal ℂ (edgeVariety E) ≤ p) :
    ∃ C : Finset (Fin n), IsHitting E C ∧ vanishingIdeal ℂ (coordinateSubspace C) ≤ p := by
  classical
  let C := Finset.univ.filter (fun i : Fin n => X i ∈ p)
  refine ⟨C, ?_, ?_⟩
  · intro e he
    have hm : edgeMonomial e ∈ p := hEp (by
      intro x hx
      obtain ⟨i, hi, hx0⟩ := (edge_mem E x).mp hx e he
      simp only [edgeMonomial, map_prod, aeval_X]
      exact Finset.prod_eq_zero hi hx0)
    letI : p.IsPrime := hp
    obtain ⟨i, hi, hip⟩ := (Ideal.IsPrime.prod_mem_iff.mp hm)
    exact ⟨i, Finset.mem_inter.mpr ⟨by simp [C, hip], hi⟩⟩
  · have h : zeroLocus ℂ p ⊆ coordinateSubspace C := by
      intro x hx i hi
      have hip : X i ∈ p := (Finset.mem_filter.mp hi).2
      simpa using hx (X i) hip
    simpa using vanishingIdeal_anti_mono (k := ℂ) h

lemma minimal_prime_coordinate (E : Finset (Finset (Fin n)))
    (p : Ideal (MvPolynomial (Fin n) ℂ))
    (hp : p ∈ (vanishingIdeal ℂ (edgeVariety E)).minimalPrimes) :
    ∃ C : Finset (Fin n), IsMinimalHitting E C ∧ p = vanishingIdeal ℂ (coordinateSubspace C) := by
  obtain ⟨C, hC, hCp⟩ := prime_has_hitting E p hp.isPrime hp.le
  have hEq : p = vanishingIdeal ℂ (coordinateSubspace C) :=
    le_antisymm (hp.2 ⟨coord_prime C, vanishingIdeal_anti_mono (coord_subset_edge E C hC)⟩ hCp) hCp
  refine ⟨C, ⟨hC, ?_⟩, hEq⟩
  intro D hDC hD
  have hCD : coordinateSubspace D ⊆ coordinateSubspace C := by
    have hDP : vanishingIdeal ℂ (coordinateSubspace D) ≤ p := by
      rw [hEq]
      exact vanishingIdeal_anti_mono ((coord_subset_iff C D).mpr hDC)
    have hPD := hp.2 ⟨coord_prime D, vanishingIdeal_anti_mono (coord_subset_edge E D hD)⟩ hDP
    intro x hx i hi
    have hXi : X i ∈ p := by
      rw [hEq]
      intro y hy
      simpa using hy i hi
    have := hPD hXi x hx
    simpa using this
  exact Finset.Subset.antisymm hDC ((coord_subset_iff D C).mp hCD)

lemma coord_zeroLocus (C : Finset (Fin n)) :
    zeroLocus ℂ (vanishingIdeal ℂ (coordinateSubspace C)) = coordinateSubspace C := by
  apply Set.Subset.antisymm
  · intro x hx i hi
    have hm : X i ∈ vanishingIdeal ℂ (coordinateSubspace C) := by
      intro y hy
      simpa using hy i hi
    simpa using hx _ hm
  · exact zeroLocus_vanishingIdeal_le _

lemma coordinate_component_iff (E : Finset (Finset (Fin n))) (C : Finset (Fin n)) :
    coordinateSubspace C ∈ components (edgeVariety E) ↔ IsMinimalHitting E C := by
  constructor
  · rintro ⟨p, hp, heq⟩
    obtain ⟨D, hD, rfl⟩ := minimal_prime_coordinate E p hp
    rw [zeroSet_eq_zeroLocus, coord_zeroLocus] at heq
    exact (coord_injective heq) ▸ hD
  · intro hC
    refine ⟨vanishingIdeal ℂ (coordinateSubspace C), ?_, ?_⟩
    · refine ⟨⟨coord_prime C, vanishingIdeal_anti_mono (coord_subset_edge E C hC.1)⟩, ?_⟩
      intro p hp hpC
      obtain ⟨D, hD, hDp⟩ := prime_has_hitting E p hp.1 hp.2
      have hsub : D ⊆ C := (coord_subset_iff C D).mp (by
        intro x hx i hi
        have hXi : X i ∈ vanishingIdeal ℂ (coordinateSubspace D) := by
          intro y hy
          simpa using hy i hi
        simpa using hpC (hDp hXi) x hx)
      have hDC := hC.2 D hsub hD
      simpa [hDC] using hDp
    · rw [zeroSet_eq_zeroLocus, coord_zeroLocus]

lemma component_exists_coordinate (E : Finset (Finset (Fin n)))
    (Z : Set (Fin n → ℂ)) (hZ : Z ∈ components (edgeVariety E)) :
    ∃ C, IsMinimalHitting E C ∧ coordinateSubspace C = Z := by
  obtain ⟨p, hp, rfl⟩ := hZ
  obtain ⟨C, hC, rfl⟩ := minimal_prime_coordinate E p hp
  exact ⟨C, hC, by rw [zeroSet_eq_zeroLocus, coord_zeroLocus]⟩

end
end AlgebraicFPT.HittingSet


theorem solution (n : ℕ) (E : Finset (Finset (Fin n))) :
    (∀ C : Finset (Fin n),
      (AlgebraicFPT.HittingSet.coordinateSubspace C ∈
        AlgebraicFPT.HittingSet.components (AlgebraicFPT.HittingSet.edgeVariety E) ↔
        AlgebraicFPT.HittingSet.IsMinimalHitting E C)) ∧
    (∀ C : Finset (Fin n),
      AlgebraicFPT.HittingSet.HasCodim (AlgebraicFPT.HittingSet.coordinateSubspace C) C.card) ∧
    Set.BijOn AlgebraicFPT.HittingSet.coordinateSubspace
      {C | AlgebraicFPT.HittingSet.IsMinimalHitting E C}
      (AlgebraicFPT.HittingSet.components (AlgebraicFPT.HittingSet.edgeVariety E)) := by
  refine ⟨AlgebraicFPT.HittingSet.coordinate_component_iff E,
    AlgebraicFPT.HittingSet.coord_codim, ?_⟩
  refine ⟨?_, AlgebraicFPT.HittingSet.coord_injective.injOn, ?_⟩
  · intro C hC
    exact (AlgebraicFPT.HittingSet.coordinate_component_iff E C).mpr hC
  · intro Z hZ
    exact AlgebraicFPT.HittingSet.component_exists_coordinate E Z hZ
