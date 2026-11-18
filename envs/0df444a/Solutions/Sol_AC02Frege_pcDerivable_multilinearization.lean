-- Prove2me | solution 1 for AC02Frege.pcDerivable_multilinearization
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-11-17T11:56:32.040612+00:00
-- url     : https://prove2.me/submissions/dc0004e9-9bb0-4431-8ced-f455b52dc5a6

import Definitions.Def_AC02Frege_PC

open MvPolynomial

namespace AC02Frege.Support

theorem derivation_append {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K))
    {π ρ : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π)
    (hρ : PCNonBool.IsDerivation red P ρ) :
    PCNonBool.IsDerivation red P (π ++ ρ) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left
      simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    have hk' : k < ρ.length := by simp only [List.length_append] at hk; omega
    have hget (t : ℕ) (ht : t < ρ.length) :
        (π ++ ρ)[π.length + t]'(by simp only [List.length_append]; omega) = ρ[t] := by
      rw [List.getElem_append_right (Nat.le_add_right π.length t)]
      simp only [Nat.add_sub_cancel_left]
    rcases hρ k hk' with ha | hc | hm
    · left
      obtain ⟨a, ha, c, hac⟩ := ha
      exact ⟨a, ha, c, (hget k hk').trans hac⟩
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨π.length + i, π.length + j, by omega, by omega, a, b, ?_⟩
      rw [hget k hk', hget i (hi.trans hk'), hget j (hj.trans hk')]
      exact hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨π.length + i, by omega, v, ?_⟩
      rw [hget k hk', hget i (hi.trans hk')]
      exact hiv

theorem derivation_snoc {σ K : Type*} [Field K]
    (red : MvPolynomial σ K →ₗ[K] MvPolynomial σ K)
    (P : Set (MvPolynomial σ K)) {π : List (MvPolynomial σ K)}
    (hπ : PCNonBool.IsDerivation red P π) (p : MvPolynomial σ K)
    (hp :
      (∃ a ∈ P, ∃ c : K, p = c • red a) ∨
      (∃ (i j : ℕ) (hi : i < π.length) (hj : j < π.length) (a b : K),
        p = a • π[i] + b • π[j]) ∨
      (∃ (i : ℕ) (hi : i < π.length) (v : σ), p = red (X v * π[i]))) :
    PCNonBool.IsDerivation red P (π ++ [p]) := by
  intro k hk
  by_cases h : k < π.length
  · rcases hπ k h with ha | hc | hm
    · left; simpa only [List.getElem_append_left h] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h),
        List.getElem_append_left (hj.trans h)] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [List.getElem_append_left h,
        List.getElem_append_left (hi.trans h)] using hiv
  · have heq : k = π.length := by simp only [List.length_append, List.length_singleton] at hk; omega
    subst k
    have hlast : (π ++ [p])[π.length] = p := by
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    rcases hp with ha | hc | hm
    · left; simpa only [hlast] using ha
    · right; left
      obtain ⟨i, j, hi, hj, a, b, hab⟩ := hc
      refine ⟨i, j, hi, hj, a, b, ?_⟩
      simpa only [hlast, List.getElem_append_left hi, List.getElem_append_left hj] using hab
    · right; right
      obtain ⟨i, hi, v, hiv⟩ := hm
      refine ⟨i, hi, v, ?_⟩
      simpa only [hlast, List.getElem_append_left hi] using hiv

theorem pc_zero {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ) :
    PCDerivable F D 0 := Or.inl rfl

theorem pc_degree {n : ℕ} {F : LiftSAParity.CNF (Fin n)} {D : ℕ}
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) : p.totalDegree ≤ D := by
  rcases hp with rfl | ⟨π, _, hdeg, hp⟩
  · simp
  · exact hdeg p hp

theorem pc_smul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p) (c : ZMod 2) :
    PCDerivable F D (c • p) := by
  rcases hp with rfl | ⟨π, hπ, hdeg, hp⟩
  · simp only [smul_zero]; exact pc_zero F D
  · obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
    refine Or.inr ⟨π ++ [c • p], ?_, ?_, by simp⟩
    · apply derivation_snoc _ _ hπ
      right; left
      exact ⟨i, i, hi, hi, c, 0, by simp only [hpi, zero_smul, add_zero]⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hdeg q hq
      · have heq : q = c • p := List.mem_singleton.mp hq
        subst q
        exact (totalDegree_smul_le c p).trans (hdeg p hp)

theorem pc_add {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p q : MvPolynomial (Fin n) (ZMod 2)}
    (hp : PCDerivable F D p) (hq : PCDerivable F D q) :
    PCDerivable F D (p + q) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simpa only [zero_add] using hq
  rcases hq with rfl | ⟨ρ, hρ, hρdeg, hq⟩
  · simpa only [add_zero] using (show PCDerivable F D p from Or.inr ⟨π, hπ, hπdeg, hp⟩)
  have hboth := derivation_append _ _ hπ hρ
  have hp' : p ∈ π ++ ρ := List.mem_append_left _ hp
  have hq' : q ∈ π ++ ρ := List.mem_append_right _ hq
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp'
  obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hq'
  refine Or.inr ⟨(π ++ ρ) ++ [p + q], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hboth
    right; left
    exact ⟨i, j, hi, hj, 1, 1, by simp only [hpi, hqj, one_smul]⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact hπdeg r hr
      · exact hρdeg r hr
    · have heq : r = p + q := List.mem_singleton.mp hr
      subst r
      exact (totalDegree_add p q).trans (max_le (hπdeg p hp) (hρdeg q hq))

theorem pc_mul_X {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    {p : MvPolynomial (Fin n) (ZMod 2)} (hp : PCDerivable F D p)
    (v : Fin n) (hdeg : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (p * X v) := by
  rcases hp with rfl | ⟨π, hπ, hπdeg, hp⟩
  · simp only [zero_mul]; exact pc_zero F D
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  refine Or.inr ⟨π ++ [p * X v], ?_, ?_, by simp⟩
  · apply derivation_snoc _ _ hπ
    right; right
    exact ⟨i, hi, v, by simp only [hpi, LinearMap.id_apply, mul_comm]⟩
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hπdeg q hq
    · have heq : q = p * X v := List.mem_singleton.mp hq
      subst q
      exact (totalDegree_mul p (X v)).trans (by simpa only [totalDegree_X] using hdeg)

theorem pc_axiom {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : p ∈ pcAxioms F)
    (hdeg : p.totalDegree ≤ D) : PCDerivable F D p := by
  refine Or.inr ⟨[p], ?_, by simpa using hdeg, by simp⟩
  intro k hk
  have heq : k = 0 := by simpa using hk
  subst k
  left
  exact ⟨p, hp, 1, by simp⟩

end AC02Frege.Support

open MvPolynomial
open AC02Frege AC02Frege.Support

theorem pc_polynomial_mul {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (u v : MvPolynomial (Fin n) (ZMod 2)) (hu : PCDerivable F D u)
    (hdeg : u.totalDegree + v.totalDegree ≤ D) : PCDerivable F D (u * v) := by
  classical
  induction v using MvPolynomial.induction_on'' with
  | C c =>
    simpa only [mul_comm u (C c), ← smul_eq_C_mul] using pc_smul F D hu c
  | monomial_add s c p hnot hc ihp ihm =>
    have hdis : Disjoint (monomial s c).support p.support := by
      apply disjoint_support_monomial
      · exact hnot
      · exact hc
    have hsupp : (monomial s c + p).support = (monomial s c).support ∪ p.support := by
      exact Finsupp.support_add_eq hdis
    have hdm : (monomial s c).totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_left
    have hdp : p.totalDegree ≤ (monomial s c + p).totalDegree := by
      apply totalDegree_le_of_support_subset
      rw [hsupp]
      exact Finset.subset_union_right
    rw [mul_add]
    exact pc_add F D (ihm (by omega)) (ihp (by omega))
  | mul_X p i ih =>
    by_cases hp : p = 0
    · simp only [hp, zero_mul, mul_zero]; exact pc_zero F D
    have hdp : (p * X i).totalDegree = p.totalDegree + 1 := by
      rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
    have hbound : u.totalDegree + p.totalDegree + 1 ≤ D := by omega
    have hmul : (u * p).totalDegree + 1 ≤ D := by
      have := totalDegree_mul u p
      omega
    simpa only [mul_assoc] using pc_mul_X F D (ih (by omega)) i hmul

open MvPolynomial AC02Frege AC02Frege.Support

private theorem ml_monomial_formula {V : Type*} (s : V →₀ ℕ) (c : ZMod 2) :
    ML (monomial s c) = monomial (sqfree s) c := by
  have h := (basisMonomials V (ZMod 2)).constr_basis (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) s
  have hc : monomial s c = c • monomial s (1 : ZMod 2) := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul]
  change c • ((basisMonomials V (ZMod 2)).constr (ZMod 2)
    (fun t => monomial (sqfree t) (1 : ZMod 2)) (monomial s 1)) = _
  rw [show monomial s (1 : ZMod 2) = basisMonomials V (ZMod 2) s by rfl, h]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

private theorem monomial_reduction {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (s : Fin n →₀ ℕ) (c : ZMod 2) (hdeg : s.sum (fun _ e => e) ≤ D) :
    PCDerivable F D (monomial s c + monomial (sqfree s) c) := by
  classical
  induction hs : s.sum (fun _ e => e) using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases hsq : ∀ i, s i ≤ 1
    · have heq : sqfree s = s := by
        ext i
        simp only [sqfree, Finsupp.mapRange_apply, min_eq_left (hsq i)]
      rw [heq, CharTwo.add_self_eq_zero]
      exact pc_zero F D
    obtain ⟨i, hi⟩ := not_forall.mp hsq
    have hi2 : 2 ≤ s i := by omega
    let r : Fin n →₀ ℕ := s - Finsupp.single i 2
    have hle : Finsupp.single i 2 ≤ s := by
      intro j
      by_cases hj : j = i
      · subst j; simpa using hi2
      · simp [Finsupp.single_apply, hj]
    have heq : r + Finsupp.single i 2 = s := tsub_add_cancel_of_le hle
    let t : Fin n →₀ ℕ := r + Finsupp.single i 1
    have hsum : r.sum (fun _ e => e) + 2 = s.sum (fun _ e => e) := by
      have h := congrArg (fun z : Fin n →₀ ℕ => z.sum (fun _ e => e)) heq
      simpa [Finsupp.sum_add_index'] using h
    have htsum : t.sum (fun _ e => e) = r.sum (fun _ e => e) + 1 := by
      simp [t, Finsupp.sum_add_index']
    have hsqeq : sqfree t = sqfree s := by
      rw [← heq]
      ext j
      by_cases hj : j = i
      · subst j
        simp only [sqfree, Finsupp.mapRange_apply, t, Finsupp.add_apply,
          Finsupp.single_eq_same]
        omega
      · simp [sqfree, Finsupp.mapRange_apply, t, Finsupp.single_apply, hj]
    have hBdeg : (X i ^ 2 + X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 2 := by
      have h := totalDegree_add (X i ^ 2 : MvPolynomial (Fin n) (ZMod 2)) (X i)
      simpa only [totalDegree_X_pow, totalDegree_X, max_eq_left (by omega : 1 ≤ 2)] using h
    have hB : PCDerivable F D (X i ^ 2 + X i) :=
      pc_axiom F D _ (Or.inr ⟨i, rfl⟩) (by omega)
    have hstep : PCDerivable F D (monomial s c + monomial t c) := by
      have hprod := pc_polynomial_mul F D (X i ^ 2 + X i) (monomial r c) hB
        (by
          have hrdeg : (monomial r c : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
              r.sum (fun _ e => e) := totalDegree_monomial_le r c
          omega)
      have hfactor : monomial s c + monomial t c =
          monomial r c * (X i ^ 2 + X i) := by
        calc
          monomial s c + monomial t c =
            monomial (r + Finsupp.single i 2) c +
              monomial (r + Finsupp.single i 1) c := by rw [heq]
          _ = monomial r c * (X i ^ 2 + X i) := by
            simp only [monomial_add_single, pow_one, mul_add]
      rw [hfactor]
      simpa only [mul_comm] using hprod
    have htdeg : t.sum (fun _ e => e) ≤ D := by omega
    have htlt : t.sum (fun _ e => e) < k := by omega
    have hrec := ih _ htlt t htdeg rfl
    have hresult := pc_add F D hstep hrec
    simpa only [hsqeq, add_assoc, CharTwo.add_cancel_left] using hresult

theorem solution {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (D : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : PCDerivable F D p) :
    PCDerivable F D (ML p) := by
  classical
  have hdiff : PCDerivable F D (p + ML p) := by
    have hmono : ∀ s ∈ p.support,
        PCDerivable F D (monomial s (coeff s p) + monomial (sqfree s) (coeff s p)) := by
      intro s hs
      exact monomial_reduction F D s (coeff s p) ((le_totalDegree hs).trans (pc_degree hp))
    have hsum : ∀ (S : Finset (Fin n →₀ ℕ)), S ⊆ p.support →
        PCDerivable F D (∑ s ∈ S,
          (monomial s (coeff s p) + monomial (sqfree s) (coeff s p))) := by
      intro S
      induction S using Finset.induction_on with
      | empty => intro _; simpa using pc_zero F D
      | @insert s S hs ih =>
        intro hsub
        rw [Finset.sum_insert hs]
        exact pc_add F D (hmono s (hsub (by simp)))
          (ih (fun a ha => hsub (by simp [ha])))
    have h := hsum p.support (fun _ h => h)
    have heq : p + ML p = ∑ s ∈ p.support,
        (monomial s (coeff s p) + monomial (sqfree s) (coeff s p)) := by
      rw [Finset.sum_add_distrib, support_sum_monomial_coeff]
      congr 1
      conv_lhs => rw [p.as_sum]
      simp only [map_sum, ml_monomial_formula]
    rw [heq]
    exact h
  have h := pc_add F D hp hdiff
  simpa only [CharTwo.add_cancel_left] using h
