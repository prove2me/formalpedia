-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupport
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:27.977804+00:00
-- url     : https://prove2.me/theorems/2e598157-89a6-40eb-84bb-a82370739974
-- title:
--   Det Frobenius Sub Pow Support
-- statement:
--   Definitions and structural lemmas for Det Frobenius Sub Pow Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetFrobeniusSubPowSupport.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh MvPolynomial
namespace GlobalTheory.DetPowDegree
variable {α : Type} [Fintype α]
def Good (l : ℤ) (L E n d s : ℕ) (p : MvPolynomial (α ⊕ α) ℤ) : Prop :=
  ∀ m : (α ⊕ α) →₀ ℕ, coeff m p ≠ 0 → (∑ q, m (Sum.inr q)) ≤ n ∧
    (∑ q, m (Sum.inl q)) + L * ∑ q, m (Sum.inr q) = d ∧
    l ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ coeff m p
variable {l : ℤ} {L E : ℕ}
theorem Good.dvd {n d s : ℕ} {p : MvPolynomial (α ⊕ α) ℤ} (h : Good l L E n d s p)
    (m : (α ⊕ α) →₀ ℕ) :
    l ^ (E * (∑ q, m (Sum.inr q)) + (s - ∑ q, m (Sum.inr q))) ∣ coeff m p := by
  by_cases hm : coeff m p = 0
  · rw [hm]; exact dvd_zero _
  · exact (h m hm).2.2
theorem Good.zero {n d s : ℕ} : Good (α := α) l L E n d s 0 := fun m hm => by simp at hm
theorem Good.add {n d s : ℕ} {p q : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p)
    (hq : Good l L E n d s q) : Good l L E n d s (p + q) := by
  intro m hm
  rw [coeff_add] at hm ⊢
  have h3 := dvd_add (hp.dvd m) (hq.dvd m)
  by_cases h : coeff m p = 0
  · have h' : coeff m q ≠ 0 := by simpa [h] using hm
    exact ⟨(hq m h').1, (hq m h').2.1, h3⟩
  · exact ⟨(hp m h).1, (hp m h).2.1, h3⟩
theorem Good.mul {n d s n' d' s' : ℕ} {p q : MvPolynomial (α ⊕ α) ℤ} (hp : Good l L E n d s p)
    (hq : Good l L E n' d' s' q) : Good l L E (n + n') (d + d') (s + s') (p * q) := by
  classical
  intro m hm
  rw [coeff_mul] at hm ⊢
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have h1 := hp _ (left_ne_zero_of_mul hx0)
  have h2 := hq _ (right_ne_zero_of_mul hx0)
  have key : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal m, ∀ f : α → α ⊕ α,
      (∑ q, m (f q)) = (∑ q, y.1 (f q)) + ∑ q, y.2 (f q) := by
    intro y hy f
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    rw [← hy, ← Finset.sum_add_distrib]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [key x hx]; omega
  · rw [key x hx, key x hx Sum.inr, ← h1.2.1, ← h2.2.1]; ring
  · refine Finset.dvd_sum fun y hy => ?_
    refine dvd_trans ?_ (mul_dvd_mul (hp.dvd y.1) (hq.dvd y.2))
    rw [← pow_add, key y hy Sum.inr]
    apply pow_dvd_pow
    rw [mul_add]
    omega
theorem Good.C (a : ℤ) : Good (α := α) l L E 0 0 0 (C a) := by
  classical
  intro m hm
  rw [coeff_C] at hm
  have h : 0 = m := by
    by_contra h
    simp [h] at hm
  subst h
  simp
theorem Good.sum {ι : Type} {n d s : ℕ} (t : Finset ι) (f : ι → MvPolynomial (α ⊕ α) ℤ)
    (h : ∀ i ∈ t, Good l L E n d s (f i)) : Good l L E n d s (∑ i ∈ t, f i) :=
  Finset.sum_induction f _ (fun _ _ => Good.add) Good.zero h
theorem Good.prod {ι : Type} {n d : ℕ} (t : Finset ι) (f : ι → MvPolynomial (α ⊕ α) ℤ)
    (h : ∀ i ∈ t, Good l L E n d 0 (f i)) :
    Good l L E (t.card * n) (t.card * d) 0 (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using Good.C (α := α) (l := l) (L := L) (E := E) 1
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_mul, add_mul, one_mul, one_mul,
      add_comm, add_comm _ d]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem Good.det {k n d : ℕ} (M : Matrix (Fin k) (Fin k) (MvPolynomial (α ⊕ α) ℤ))
    (h : ∀ i j, Good l L E n d 0 (M i j)) : Good l L E (k * n) (k * d) 0 M.det := by
  rw [Matrix.det_apply']
  refine Good.sum _ _ fun σ _ => ?_
  have h1 := Good.prod (l := l) (L := L) (E := E) (n := n) (d := d) Finset.univ
    (fun i => M (σ i) i) (fun i _ => h _ _)
  have h2 := (Good.C (α := α) (l := l) (L := L) (E := E) (Equiv.Perm.sign σ : ℤ)).mul h1
  simpa using h2
def freeIdeal (α : Type) [Fintype α] (l : ℤ) : Ideal (MvPolynomial (α ⊕ α) ℤ) where
  carrier := {p | ∀ m : (α ⊕ α) →₀ ℕ, (∑ q, m (Sum.inr q)) = 0 → l ∣ coeff m p}
  add_mem' := fun {p q} hp hq m hm => by
    rw [coeff_add]; exact dvd_add (hp m hm) (hq m hm)
  zero_mem' := fun m _ => by simp
  smul_mem' := fun c p hp m hm => by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Finset.dvd_sum fun y hy => Dvd.dvd.mul_left (hp y.2 ?_) _
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
    rw [← hy] at hm
    simp only [Finsupp.add_apply, Finset.sum_add_distrib] at hm
    omega
end GlobalTheory.DetPowDegree
namespace GlobalTheory
end GlobalTheory


