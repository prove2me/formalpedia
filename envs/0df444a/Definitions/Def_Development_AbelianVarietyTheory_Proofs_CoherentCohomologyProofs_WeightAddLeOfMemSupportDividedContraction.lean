-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:57.238868+00:00
-- url     : https://prove2.me/theorems/27cb3158-1485-4381-bb6d-c4af8f4a8621
-- title:
--   Weight Add Le Of Mem Support Divided Contraction
-- statement:
--   Definitions and structural lemmas for Weight Add Le Of Mem Support Divided Contraction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.Wick
section Eval
variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A] {σ ι κ : Type*}
open scoped IsMulCommutative in

noncomputable def commEval (k : Type*) [CommSemiring k] [Algebra k A] (a : σ → A)
    (ha : ∀ i j, Commute (a i) (a j)) : MvPolynomial σ k →ₐ[k] A :=
  haveI : IsMulCommutative (Algebra.adjoin k (Set.range a)) :=
    Algebra.isMulCommutative_adjoin k (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact ha i j)
  (Algebra.adjoin k (Set.range a)).val.comp
    (aeval fun i => (⟨a i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : Algebra.adjoin k (Set.range a)))
@[simp] theorem commEval_X (a : σ → A) (ha : ∀ i j, Commute (a i) (a j)) (i : σ) :
    commEval k a ha (X i) = a i := by
  simp [commEval]
@[simp] theorem commEval_C (a : σ → A) (ha : ∀ i j, Commute (a i) (a j)) (c : k) :
    commEval k a ha (C c) = algebraMap k A c := algHom_C _ _
theorem commute_commEval {a : σ → A} (ha : ∀ i j, Commute (a i) (a j)) {b : A}
    (hb : ∀ i, Commute b (a i)) (P : MvPolynomial σ k) : Commute b (commEval k a ha P) := by
  induction P using MvPolynomial.induction_on with
  | C c => rw [commEval_C]; exact (Algebra.commutes c b).symm
  | add P Q hP hQ => rw [map_add]; exact hP.add_right hQ
  | mul_X P i hP => rw [map_mul, commEval_X]; exact hP.mul_right (hb i)
theorem commute_mulLeft_mulRight {a : ι → A} {a' : κ → A} (ha : ∀ i j, Commute (a i) (a j))
    (ha' : ∀ i j, Commute (a' i) (a' j)) (v w : ι ⊕ κ) :
    Commute (Sum.elim (fun i => LinearMap.mulLeft k (a i)) (fun j => LinearMap.mulRight k (a' j)) v :
      Module.End k A)
      (Sum.elim (fun i => LinearMap.mulLeft k (a i)) (fun j => LinearMap.mulRight k (a' j)) w) := by
  rcases v with v | v <;> rcases w with w | w <;> refine LinearMap.ext fun z => ?_
  · simp [← mul_assoc, (ha v w).eq]
  · simp [mul_assoc]
  · simp [mul_assoc]
  · simp [mul_assoc, (ha' v w).eq]
noncomputable def orderedEval (k : Type*) [CommSemiring k] [Algebra k A] (a : ι → A) (a' : κ → A)
    (ha : ∀ i j, Commute (a i) (a j)) (ha' : ∀ i j, Commute (a' i) (a' j)) :
    MvPolynomial (ι ⊕ κ) k →ₗ[k] A :=
  LinearMap.applyₗ (1 : A) ∘ₗ
    (commEval k _ (commute_mulLeft_mulRight (k := k) ha ha')).toLinearMap
variable {a : ι → A} {a' : κ → A} (ha : ∀ i j, Commute (a i) (a j))
  (ha' : ∀ i j, Commute (a' i) (a' j))
@[simp] theorem orderedEval_C (c : k) : orderedEval k a a' ha ha' (C c) = algebraMap k A c := by
  simp [orderedEval, Algebra.algebraMap_eq_smul_one]
@[simp] theorem orderedEval_one : orderedEval k a a' ha ha' 1 = 1 := by
  rw [← C_1, orderedEval_C, map_one]
end Eval
section Divided
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : Type*}
def multiChoose (n β : σ →₀ ℕ) : ℕ := β.prod fun i e => (n i).choose e
def multiFactorial (β : σ →₀ ℕ) : ℕ := β.prod fun _ e => e.factorial
@[simp] theorem multiChoose_zero (n : σ →₀ ℕ) : multiChoose n 0 = 1 := by simp [multiChoose]
theorem multiChoose_eq_mul_erase (n β : σ →₀ ℕ) (i : σ) :
    multiChoose n β = (n i).choose (β i) * multiChoose n (β.erase i) :=
  (Finsupp.mul_prod_erase' β i _ fun _ => Nat.choose_zero_right _).symm
theorem multiChoose_add_single_left {β : σ →₀ ℕ} {i : σ} (h : β i = 0) (n : σ →₀ ℕ) (e : ℕ) :
    multiChoose (n + Finsupp.single i e) β = multiChoose n β := by
  refine Finsupp.prod_congr fun j hj => ?_
  have : i ≠ j := by rintro rfl; exact Finsupp.mem_support_iff.mp hj h
  simp [Finsupp.single_eq_of_ne' this]
theorem le_of_multiChoose_ne_zero {n β : σ →₀ ℕ} (h : multiChoose n β ≠ 0) : β ≤ n := by
  intro i
  rw [multiChoose_eq_mul_erase n β i] at h
  by_contra hi
  exact h (by rw [Nat.choose_eq_zero_of_lt (not_le.mp hi), zero_mul])
theorem erase_add_single_self (β : σ →₀ ℕ) (i : σ) (e : ℕ) :
    (β + Finsupp.single i e).erase i = β.erase i := by
  rw [Finsupp.erase_add, Finsupp.erase_single, add_zero]
theorem multiChoose_pascal (n β : σ →₀ ℕ) (i : σ) :
    multiChoose (n + Finsupp.single i 1) (β + Finsupp.single i 1) =
      multiChoose n (β + Finsupp.single i 1) + multiChoose n β := by
  rw [multiChoose_eq_mul_erase _ _ i, multiChoose_eq_mul_erase n (β + _) i,
    multiChoose_eq_mul_erase n β i, erase_add_single_self,
    multiChoose_add_single_left Finsupp.erase_same]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.choose_succ_succ', add_mul]
  ring
theorem multiChoose_mul_sub (n β : σ →₀ ℕ) (i : σ) :
    multiChoose n β * (n i - β i) = (β i + 1) * multiChoose n (β + Finsupp.single i 1) := by
  rw [multiChoose_eq_mul_erase n (β + _) i, multiChoose_eq_mul_erase n β i, erase_add_single_self]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  have := Nat.choose_succ_right_eq (n i) (β i)
  calc _ = (n i).choose (β i) * (n i - β i) * multiChoose n (β.erase i) := by ring
    _ = _ := by rw [← this]; ring
variable (R) in

noncomputable def dividedDeriv (β : σ →₀ ℕ) : Module.End R (MvPolynomial σ R) :=
  (basisMonomials σ R).constr R fun n => multiChoose n β • monomial (n - β) 1
theorem dividedDeriv_monomial (β n : σ →₀ ℕ) (c : R) :
    dividedDeriv R β (monomial n c) = multiChoose n β • monomial (n - β) c := by
  have h : (monomial n c : MvPolynomial σ R) = c • basisMonomials σ R n := by
    simp [smul_monomial]
  rw [h, map_smul, dividedDeriv, Module.Basis.constr_basis, smul_comm, smul_monomial, smul_eq_mul,
    mul_one]
theorem coeff_dividedDeriv (β m : σ →₀ ℕ) (P : MvPolynomial σ R) :
    coeff m (dividedDeriv R β P) = multiChoose (m + β) β • coeff (m + β) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [dividedDeriv_monomial, coeff_smul, coeff_monomial, coeff_monomial]
    by_cases h : n = m + β
    · subst h; simp
    · rw [if_neg h, smul_zero]
      by_cases h0 : multiChoose n β = 0
      · rw [h0, zero_smul]
      · rw [if_neg, smul_zero]
        rintro rfl
        exact h (tsub_add_cancel_of_le (le_of_multiChoose_ne_zero h0)).symm
  | add P Q hP hQ => simp only [map_add, coeff_add, hP, hQ, smul_add]
@[simp] theorem dividedDeriv_zero : dividedDeriv R (0 : σ →₀ ℕ) = 1 := by
  refine LinearMap.ext fun P => MvPolynomial.ext _ _ fun m => ?_
  simp [coeff_dividedDeriv]
theorem pderiv_dividedDeriv (β : σ →₀ ℕ) (i : σ) (P : MvPolynomial σ R) :
    pderiv i (dividedDeriv R β P) = (β i + 1) • dividedDeriv R (β + Finsupp.single i 1) P := by
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [dividedDeriv_monomial, dividedDeriv_monomial, map_nsmul, pderiv_monomial, smul_smul,
      ← multiChoose_mul_sub, tsub_tsub, mul_smul, smul_monomial (n i - β i)]
    simp [mul_comm]
  | add P Q hP hQ => simp only [map_add, hP, hQ, smul_add]
theorem dividedDeriv_single_one (i : σ) (P : MvPolynomial σ R) :
    dividedDeriv R (Finsupp.single i 1) P = pderiv i P := by
  simpa using (pderiv_dividedDeriv 0 i P).symm
theorem pderiv_pderiv_comm (i j : σ) (P : MvPolynomial σ R) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  by_cases h : i = j
  · rw [h]
  · rw [← dividedDeriv_single_one j, ← dividedDeriv_single_one i P, pderiv_dividedDeriv,
      pderiv_dividedDeriv, add_comm (Finsupp.single j 1), Finsupp.single_eq_of_ne h,
      Finsupp.single_eq_of_ne' h]
theorem commute_pderiv (i j : σ) :
    Commute ((pderiv i).toLinearMap : Module.End R (MvPolynomial σ R)) (pderiv j).toLinearMap :=
  LinearMap.ext fun P => pderiv_pderiv_comm i j P
theorem dividedDeriv_add_single_X_mul (β : σ →₀ ℕ) (i : σ) (P : MvPolynomial σ R) :
    dividedDeriv R (β + Finsupp.single i 1) (X i * P) =
      X i * dividedDeriv R (β + Finsupp.single i 1) P + dividedDeriv R β P := by
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
    have hX (m : σ →₀ ℕ) : X i * monomial m c = monomial (m + Finsupp.single i 1) c := by
      rw [monomial_add_single, pow_one, mul_comm]
    rw [hX, dividedDeriv_monomial, dividedDeriv_monomial, dividedDeriv_monomial, multiChoose_pascal,
      add_smul, add_tsub_add_eq_tsub_right, mul_smul_comm, hX]
    by_cases h0 : multiChoose n (β + Finsupp.single i 1) = 0
    · simp [h0]
    · obtain ⟨m, rfl⟩ := exists_add_of_le (le_of_multiChoose_ne_zero h0)
      rw [add_tsub_cancel_left, add_assoc β, add_tsub_cancel_left, add_comm m]
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]; abel
theorem dividedDeriv_X_mul_of_eq_zero {β : σ →₀ ℕ} {i : σ} (h : β i = 0) (P : MvPolynomial σ R) :
    dividedDeriv R β (X i * P) = X i * dividedDeriv R β P := by
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
    have hX (m : σ →₀ ℕ) : X i * monomial m c = monomial (m + Finsupp.single i 1) c := by
      rw [monomial_add_single, pow_one, mul_comm]
    rw [hX, dividedDeriv_monomial, dividedDeriv_monomial, multiChoose_add_single_left h,
      mul_smul_comm, hX]
    by_cases h0 : multiChoose n β = 0
    · simp [h0]
    · rw [tsub_add_eq_add_tsub (le_of_multiChoose_ne_zero h0)]
  | add P Q hP hQ => simp only [mul_add, map_add, hP, hQ]
end Divided
section Contraction
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
noncomputable def rowContraction (γ : ι → κ → R) (i : ι) : Module.End R (MvPolynomial (ι ⊕ κ) R) :=
  ∑ j, γ i j • (pderiv (Sum.inr j)).toLinearMap
theorem rowContraction_apply (γ : ι → κ → R) (i : ι) (P : MvPolynomial (ι ⊕ κ) R) :
    rowContraction γ i P = ∑ j, γ i j • pderiv (Sum.inr j) P := by
  simp [rowContraction, LinearMap.sum_apply]
theorem commute_pderiv_rowContraction (γ : ι → κ → R) (v : ι ⊕ κ) (i : ι) :
    Commute ((pderiv v).toLinearMap : Module.End R (MvPolynomial (ι ⊕ κ) R))
      (rowContraction γ i) :=
  Commute.sum_right _ _ _ fun _ _ => (commute_pderiv _ _).smul_right _
theorem commute_rowContraction (γ : ι → κ → R) (i i' : ι) :
    Commute (rowContraction γ i) (rowContraction γ i') :=
  Commute.sum_left _ _ _ fun _ _ => (commute_pderiv_rowContraction _ _ _).smul_left _
theorem rowContraction_X_inl_mul (γ : ι → κ → R) (i i' : ι) (P : MvPolynomial (ι ⊕ κ) R) :
    rowContraction γ i (X (Sum.inl i') * P) = X (Sum.inl i') * rowContraction γ i P := by
  classical
  simp [rowContraction_apply, Finset.mul_sum, pderiv_X]
@[simp] theorem rowContraction_C (γ : ι → κ → R) (i : ι) (c : R) :
    rowContraction γ i (C c) = 0 := by
  simp [rowContraction_apply]
variable [Fintype ι]
noncomputable def contraction (γ : ι → κ → R) : Module.End R (MvPolynomial (ι ⊕ κ) R) :=
  ∑ i, ∑ j, γ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)
open scoped Classical in

noncomputable def dividedContraction (γ : ι → κ → R) (n : ℕ) :
    Module.End R (MvPolynomial (ι ⊕ κ) R) :=
  ∑ α ∈ (Finset.univ : Finset ι).finsuppAntidiag n,
    commEval R (rowContraction γ) (commute_rowContraction γ) (monomial α 1) *
      dividedDeriv R (α.mapDomain Sum.inl)
@[simp] theorem dividedContraction_zero (γ : ι → κ → R) : dividedContraction γ 0 = 1 := by
  simp [dividedContraction]
theorem dividedContraction_succ_rename_inr (γ : ι → κ → R) (n : ℕ) (q : MvPolynomial κ R) :
    dividedContraction γ (n + 1) (rename Sum.inr q) = 0 := by
  classical
  rw [dividedContraction, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun α hα => ?_
  have hne : α ≠ 0 := by rintro rfl; simp at hα
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  suffices dividedDeriv R (α.mapDomain Sum.inl) (rename (Sum.inr : κ → ι ⊕ κ) q) = 0 by
    rw [Module.End.mul_apply, this, map_zero]
  induction q using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [rename_monomial, dividedDeriv_monomial]
    have : multiChoose (t.mapDomain (Sum.inr : κ → ι ⊕ κ)) (α.mapDomain Sum.inl) = 0 := by
      by_contra h
      have := le_of_multiChoose_ne_zero h (Sum.inl i)
      rw [Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_notin_range _ _ (by simp)]
        at this
      exact hi (Nat.le_zero.mp this)
    rw [this, zero_smul]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
theorem dividedContraction_succ_X_inl_mul (γ : ι → κ → R) (n : ℕ) (i : ι)
    (P : MvPolynomial (ι ⊕ κ) R) :
    dividedContraction γ (n + 1) (X (Sum.inl i) * P) =
      X (Sum.inl i) * dividedContraction γ (n + 1) P +
        rowContraction γ i (dividedContraction γ n P) := by
  classical
  set E := commEval R (rowContraction γ) (commute_rowContraction γ) with hE
  have hX (p : MvPolynomial ι R) (Q : MvPolynomial (ι ⊕ κ) R) :
      E p (X (Sum.inl i) * Q) = X (Sum.inl i) * E p Q :=
    (LinearMap.congr_fun (commute_commEval (commute_rowContraction γ)
      (b := LinearMap.mulLeft R (X (Sum.inl i)))
      (fun i' => LinearMap.ext fun Q => (rowContraction_X_inl_mul γ i' i Q).symm) p).eq Q).symm
  have key (α : ι →₀ ℕ) :
      E (monomial α 1) (dividedDeriv R (α.mapDomain Sum.inl) (X (Sum.inl i) * P)) =
        X (Sum.inl i) * E (monomial α 1) (dividedDeriv R (α.mapDomain Sum.inl) P) +
          if α i = 0 then 0 else rowContraction γ i (E (monomial (α - Finsupp.single i 1) 1)
            (dividedDeriv R ((α - Finsupp.single i 1).mapDomain Sum.inl) P)) := by
    split_ifs with h
    · rw [dividedDeriv_X_mul_of_eq_zero (by rwa [Finsupp.mapDomain_apply Sum.inl_injective]), hX,
        add_zero]
    · obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single i 1 :=
        ⟨α - Finsupp.single i 1, (tsub_add_cancel_of_le
          (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))).symm⟩
      rw [add_tsub_cancel_right, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
        dividedDeriv_add_single_X_mul, map_add, hX]
      congr 1
      rw [monomial_add_single, pow_one, mul_comm, map_mul, hE, commEval_X, Module.End.mul_apply]
  simp only [dividedContraction, LinearMap.sum_apply, Module.End.mul_apply, ← hE, key,
    Finset.sum_add_distrib, Finset.mul_sum, map_sum]
  congr 1
  have hsum (β : ι →₀ ℕ) : Finset.univ.sum ⇑(β + Finsupp.single i 1 : ι →₀ ℕ) =
      Finset.univ.sum ⇑β + 1 := by
    change ∑ x, (β + Finsupp.single i 1 : ι →₀ ℕ) x = ∑ x, β x + 1
    simp [Finset.sum_add_distrib, Finsupp.single_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  symm
  refine Finset.sum_nbij' (fun β => β + Finsupp.single i 1) (fun α => α - Finsupp.single i 1)
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [Finset.mem_finsuppAntidiag, Finset.mem_filter, Finset.subset_univ, and_true] at hβ ⊢
    exact ⟨by rw [hsum, hβ], by simp⟩
  · intro α hα
    simp only [Finset.mem_finsuppAntidiag, Finset.mem_filter, Finset.subset_univ, and_true] at hα ⊢
    obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single i 1 :=
      ⟨α - Finsupp.single i 1, (tsub_add_cancel_of_le
        (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hα.2))).symm⟩
    have h1 := hα.1
    rw [hsum] at h1
    rw [add_tsub_cancel_right]
    omega
  · intro β _; exact add_tsub_cancel_right _ _
  · intro α hα
    exact tsub_add_cancel_of_le
      (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hα).2))
  · intro β _; rw [add_tsub_cancel_right]
end Contraction
section Integrality
variable {R : Type*} [CommSemiring R] {ι κ : Type*}
noncomputable def degreeLeft (P : MvPolynomial (ι ⊕ κ) R) : ℕ :=
  weightedTotalDegree (Sum.elim (fun _ => 1) fun _ => 0 : ι ⊕ κ → ℕ) P
noncomputable def degreeRight (P : MvPolynomial (ι ⊕ κ) R) : ℕ :=
  weightedTotalDegree (Sum.elim (fun _ => 0) fun _ => 1 : ι ⊕ κ → ℕ) P
variable [Fintype ι] [Fintype κ]
variable {A : Type*} [CommSemiring A] [Algebra A R]
end Integrality
section Fractional
open scoped nonZeroDivisors
variable {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] {ι κ : Type*} [Fintype ι] [Fintype κ]
end Fractional
section Formula
variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M] [Module A M]
  {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι] {a b : ι → A} {a' b' : κ → A} {γ : ι → κ → k} {v : M}
end Formula
example : ∃ (a b : Unit → Module.End ℚ (Polynomial ℚ)) (a' b' : Unit → Module.End ℚ (Polynomial ℚ))
    (γ : Unit → Unit → ℚ) (v : Polynomial ℚ), v ≠ 0 ∧ γ () () = 1 ∧
    (∀ i j, Commute (a i) (a j)) ∧ (∀ i j, Commute (a i) (b j)) ∧ (∀ i j, Commute (b i) (b j)) ∧
    (∀ i j, Commute (a' i) (a' j)) ∧ (∀ i j, Commute (a' i) (b' j)) ∧
    (∀ i j, Commute (b' i) (b' j)) ∧ (∀ i j, Commute (b i) (b' j)) ∧
    (∀ i j, b i * a' j - a' j * b i = algebraMap ℚ _ (γ i j)) ∧
    (∀ i, b i • v = 0) ∧ (∀ j, b' j • v = 0) := by
  refine ⟨0, fun _ => Polynomial.derivative, fun _ => LinearMap.mulLeft ℚ Polynomial.X, 0,
    fun _ _ => 1, 1, one_ne_zero, rfl, fun _ _ => Commute.refl _, fun _ _ => Commute.zero_left _,
    fun _ _ => Commute.refl _, fun _ _ => Commute.refl _, fun _ _ => Commute.zero_right _,
    fun _ _ => Commute.refl _, fun _ _ => Commute.zero_right _, fun _ _ => ?_, fun _ => by simp,
    fun _ => by simp⟩
  refine LinearMap.ext fun p => ?_
  simp
example : dividedContraction (fun _ _ : Unit => (1 : ℤ)) 2
    (X (Sum.inl ()) * (X (Sum.inl ()) * rename Sum.inr (X () ^ 2))) = 2 := by
  rw [dividedContraction_succ_X_inl_mul, dividedContraction_succ_X_inl_mul,
    dividedContraction_succ_X_inl_mul]
  simp only [dividedContraction_succ_rename_inr]
  have h : pderiv (Sum.inr ()) (2 : MvPolynomial (Unit ⊕ Unit) ℤ) = 0 := pderiv_C (a := 2)
  simp [rowContraction_apply, pderiv_X, h]
end GlobalTheory.Wick


