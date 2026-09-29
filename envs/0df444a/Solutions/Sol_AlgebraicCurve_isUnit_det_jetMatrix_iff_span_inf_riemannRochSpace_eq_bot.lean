-- Prove2me | solution 1 for AlgebraicCurve.isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f2a792bf-7e1f-54c9-9e17-63ee717a92c8

import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 80000

section P2MPiece0
open AlgebraicCurve

namespace J2Sub

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  {M : ℕ} {P : Fin M → Place K F} {t : Fin M → F} {e : Fin M → ℕ}

theorem jetMult_eq_zero_of_forall_ne {v : Place K F} (h : ∀ i, P i ≠ v) : jetMult P v = 0 := by
  classical
  unfold jetMult
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _; exact h i

theorem jetMult_pos (i : Fin M) : 0 < jetMult P (P i) := by
  classical
  unfold jetMult
  rw [Finset.card_pos]
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem exists_row_of_lt_jetMult' (hP : IsConfluentPattern P t e) (i : Fin M) (q : ℕ)
    (hq : q < jetMult P (P i)) : ∃ i', P i' = P i ∧ e i' = q := by
  classical
  set B : Finset (Fin M) := Finset.univ.filter fun i' => P i' = P i with hB
  have hcard : B.card = jetMult P (P i) := by
    rw [hB]; unfold jetMult; convert rfl
  have hinj : Set.InjOn e (B : Set (Fin M)) := by
    intro a ha b hb hab
    have ha' : P a = P i := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' : P b = P i := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    exact hP.2.1 a b (ha'.trans hb'.symm) hab
  have hsub : B.image e ⊆ Finset.range (jetMult P (P i)) := by
    intro q' hq'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq'
    have ha' : P a = P i := (Finset.mem_filter.mp ha).2
    rw [Finset.mem_range, ← ha']
    exact hP.2.2 a
  have heq : B.image e = Finset.range (jetMult P (P i)) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_range, Finset.card_image_of_injOn hinj, hcard]
  have hmem : q ∈ B.image e := by rw [heq, Finset.mem_range]; exact hq
  obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hmem
  exact ⟨i', (Finset.mem_filter.mp hi').2, he⟩

end J2Sub

theorem J2Sub.exists_row_of_lt_jetMult {K F : Type*} [Field K] [Field F] [Algebra K F]
    {M : ℕ} {P : Fin M → Place K F} {t : Fin M → F} {e : Fin M → ℕ}
    (hP : IsConfluentPattern P t e) (i : Fin M) (q : ℕ) (hq : q < jetMult P (P i)) :
    ∃ i', P i' = P i ∧ t i' = t i ∧ e i' = q := by
  obtain ⟨i', hPi, he⟩ := J2Sub.exists_row_of_lt_jetMult' hP i q hq
  exact ⟨i', hPi, hP.1 i' i hPi, he⟩

end P2MPiece0

section P2MPiece1
open AlgebraicCurve

namespace J2Sub

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {M : ℕ}

theorem jetMult_eq_zero_of_forall_ne' {P : Fin M → Place K F} {v : Place K F} (h : ∀ i, P i ≠ v) :
    jetMult P v = 0 := by
  classical
  unfold jetMult
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _; exact h i

theorem jetDivisor_nonneg (P : Fin M → Place K F) (v : Place K F) : 0 ≤ jetDivisor P v := by
  rw [jetDivisor_apply]; exact Int.natCast_nonneg _

end J2Sub

theorem J2Sub.riemannRochSpace_sub_jetDivisor_le {K F : Type*} [Field K] [Field F] [Algebra K F]
    (A : Divisor K F) {M : ℕ} (P : Fin M → Place K F) :
    riemannRochSpace (A - jetDivisor P) ≤ riemannRochSpace A := by
  intro g hg
  rw [mem_riemannRochSpace_iff] at hg ⊢
  intro v
  rcases hg v with h0 | h
  · exact Or.inl h0
  · right
    have := J2Sub.jetDivisor_nonneg P v
    rw [Finsupp.sub_apply] at h
    omega

theorem J2Sub.mem_toValuationSubring_of_mem_riemannRochSpace {K F : Type*} [Field K] [Field F] [Algebra K F]
    {A : Divisor K F} {g : F} (hg : g ∈ riemannRochSpace A) {w : Place K F} (hA : A w = 0) :
    g ∈ w.toValuationSubring := by
  rcases eq_or_ne g 0 with h0 | hne
  · rw [h0]; exact zero_mem _
  · have h := ((mem_riemannRochSpace_iff.mp hg) w).resolve_left hne
    rw [hA, neg_zero] at h
    exact w.mem_toValuationSubring_of_ord_nonneg_alt hne h

theorem J2Sub.mem_riemannRochSpace_sub_jetDivisor_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    {A : Divisor K F} {M : ℕ} {P : Fin M → Place K F} (hA : ∀ i, A (P i) = 0)
    {g : F} (hg : g ∈ riemannRochSpace A) :
    g ∈ riemannRochSpace (A - jetDivisor P) ↔ ∀ i, g = 0 ∨ (jetMult P (P i) : ℤ) ≤ (P i).ord g := by
  constructor
  · intro h i
    rcases (mem_riemannRochSpace_iff.mp h) (P i) with h0 | h1
    · exact Or.inl h0
    · right
      rw [Finsupp.sub_apply, hA i, jetDivisor_apply] at h1
      omega
  · intro h
    rw [mem_riemannRochSpace_iff]
    intro v
    by_cases hv : ∃ i, P i = v
    · obtain ⟨i, rfl⟩ := hv
      rcases h i with h0 | h1
      · exact Or.inl h0
      · right
        rw [Finsupp.sub_apply, hA i, jetDivisor_apply]
        omega
    · push Not at hv
      rw [Finsupp.sub_apply, jetDivisor_apply, J2Sub.jetMult_eq_zero_of_forall_ne' hv, Nat.cast_zero, sub_zero]
      exact (mem_riemannRochSpace_iff.mp hg) v

end P2MPiece1

section P2MPiece2
open AlgebraicCurve

namespace P2MJ2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem taylorCoeff_zero_fun (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) (r : ℕ) :
    Place.taylorCoeff v t r (0 : F) = 0 := by
  have := Place.taylorCoeff_smul v hv ht (zero_mem _) (0 : K) r
  rwa [zero_smul, zero_mul] at this

theorem taylorCoeff_sum_smul (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) (r : ℕ)
    {M : ℕ} (f : Fin M → F) (hf : ∀ j, f j ∈ v.toValuationSubring) (c : Fin M → K) :
    Place.taylorCoeff v t r (∑ j, c j • f j) = ∑ j, c j * Place.taylorCoeff v t r (f j) := by
  classical
  have key : ∀ S : Finset (Fin M), (∑ j ∈ S, c j • f j) ∈ v.toValuationSubring ∧
      Place.taylorCoeff v t r (∑ j ∈ S, c j • f j) = ∑ j ∈ S, c j * Place.taylorCoeff v t r (f j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨by simp, by simp [taylorCoeff_zero_fun v hv ht r]⟩
    | insert j S hj ih =>
      obtain ⟨hmem, hval⟩ := ih
      have hsm : c j • f j ∈ v.toValuationSubring := by
        rw [Algebra.smul_def]; exact mul_mem (v.algebraMap_mem' _) (hf j)
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      refine ⟨add_mem hsm hmem, ?_⟩
      rw [Place.taylorCoeff_add v hv ht hsm hmem, hval, Place.taylorCoeff_smul v hv ht (hf j) (c j) r]
  exact (key Finset.univ).2

section Main

variable (A : Divisor K F) {M : ℕ} (f : Fin M → F)
  (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)

theorem mem_O (hA : ∀ i, A (P i) = 0) {g : F} (hg : g ∈ riemannRochSpace A) (i : Fin M) :
    g ∈ (P i).toValuationSubring :=
  J2Sub.mem_toValuationSubring_of_mem_riemannRochSpace hg (hA i)

theorem jetMatrix_mulVec (hfA : ∀ j, f j ∈ riemannRochSpace A)
    (hrat : ∀ i, (P i).IsRational) (ht : ∀ i, (P i).ord (t i) = 1) (hA : ∀ i, A (P i) = 0)
    (c : Fin M → K) (i : Fin M) :
    (jetMatrix P t e f).mulVec c i = Place.taylorCoeff (P i) (t i) (e i) (∑ j, c j • f j) := by
  have hfO : ∀ j, f j ∈ (P i).toValuationSubring := fun j => mem_O A P hA (hfA j) i
  rw [taylorCoeff_sum_smul (P i) (hrat i) (ht i) (e i) f hfO c, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [jetMatrix_apply, mul_comm]

theorem rows_vanish_iff (hP : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational)
    (ht : ∀ i, (P i).ord (t i) = 1) (hA : ∀ i, A (P i) = 0) {g : F} (hg : g ∈ riemannRochSpace A) :
    (∀ i, Place.taylorCoeff (P i) (t i) (e i) g = 0) ↔ g ∈ riemannRochSpace (A - jetDivisor P) := by
  rw [J2Sub.mem_riemannRochSpace_sub_jetDivisor_iff hA hg]
  constructor
  · intro h i
    by_cases hg0 : g = 0
    · exact Or.inl hg0
    · right

      have hall : ∀ q, q < jetMult P (P i) → Place.taylorCoeff (P i) (t i) q g = 0 := by
        intro q hq
        obtain ⟨i', hPi', hti', hei'⟩ := J2Sub.exists_row_of_lt_jetMult hP i q hq
        have := h i'
        rwa [hPi', hti', hei'] at this
      exact (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord (P i) (hrat i) (ht i) (mem_O A P hA hg i) hg0 _).mp hall
  · intro h i
    by_cases hg0 : g = 0
    · rw [hg0]; exact taylorCoeff_zero_fun (P i) (hrat i) (ht i) (e i)
    · rcases h i with h0 | hord
      · exact absurd h0 hg0
      · have hall := (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord (P i) (hrat i) (ht i)
          (mem_O A P hA hg i) hg0 (jetMult P (P i))).mpr hord
        exact hall (e i) (hP.2.2 i)

theorem main (hf : LinearIndependent K f) (hfA : ∀ j, f j ∈ riemannRochSpace A)
    (hP : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational)
    (ht : ∀ i, (P i).ord (t i) = 1) (hA : ∀ i, A (P i) = 0) :
    IsUnit (jetMatrix P t e f).det ↔
      Submodule.span K (Set.range f) ⊓ riemannRochSpace (A - jetDivisor P) = ⊥ := by
  classical
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have hcombspan : ∀ c : Fin M → K, (∑ j, c j • f j) ∈ Submodule.span K (Set.range f) := fun c =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hcombA : ∀ c : Fin M → K, (∑ j, c j • f j) ∈ riemannRochSpace A := fun c =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hfA j)
  constructor
  · intro hinj
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hgspan : g ∈ Submodule.span K (Set.range f) := hg.1
    have hg' : g ∈ riemannRochSpace (A - jetDivisor P) := hg.2
    have hgA : g ∈ riemannRochSpace A := J2Sub.riemannRochSpace_sub_jetDivisor_le A P hg'
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hgspan
    have hrows := (rows_vanish_iff A P t e hP hrat ht hA hgA).mpr hg'
    have hmv : (jetMatrix P t e f).mulVec c = 0 := by
      funext i
      rw [jetMatrix_mulVec A f P t e hfA hrat ht hA c i, hc]
      exact hrows i
    have hc0 : c = 0 := hinj (by rw [hmv, Matrix.mulVec_zero])
    rw [← hc, hc0]
    simp
  · intro hbot c c' hcc
    have hsub : (jetMatrix P t e f).mulVec (c - c') = 0 := by
      rw [Matrix.mulVec_sub, hcc, sub_self]
    have hrows : ∀ i, Place.taylorCoeff (P i) (t i) (e i) (∑ j, (c - c') j • f j) = 0 := fun i => by
      rw [← jetMatrix_mulVec A f P t e hfA hrat ht hA (c - c') i, hsub]
      rfl
    have hg0 : (∑ j, (c - c') j • f j) = 0 := by
      have hmem := (rows_vanish_iff A P t e hP hrat ht hA (hcombA (c - c'))).mp hrows
      have : (∑ j, (c - c') j • f j) ∈ Submodule.span K (Set.range f) ⊓ riemannRochSpace (A - jetDivisor P) :=
        ⟨hcombspan (c - c'), hmem⟩
      rw [hbot] at this
      exact (Submodule.mem_bot K).mp this
    funext j
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf (c - c') hg0 j)

end Main

end P2MJ2

open AlgebraicCurve in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (A : Divisor K F) {M : ℕ} (f : Fin M → F) (hf : LinearIndependent K f)
    (hfA : ∀ j, f j ∈ riemannRochSpace A)
    (P : Fin M → Place K F) (t : Fin M → F) (e : Fin M → ℕ)
    (hP : IsConfluentPattern P t e) (hrat : ∀ i, (P i).IsRational)
    (ht : ∀ i, (P i).ord (t i) = 1) (hA : ∀ i, A (P i) = 0) :
    IsUnit (jetMatrix P t e f).det ↔
      Submodule.span K (Set.range f) ⊓ riemannRochSpace (A - jetDivisor P) = ⊥ :=
  P2MJ2.main A f P t e hf hfA hP hrat ht hA

end P2MPiece2

end S_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot
end P2MW
export P2MW.S_AlgebraicCurve_isUnit_det_jetMatrix_iff_span_inf_riemannRochSpace_eq_bot (solution)
