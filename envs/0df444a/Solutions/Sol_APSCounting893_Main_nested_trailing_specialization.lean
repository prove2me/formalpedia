-- Prove2me | solution 1 for APSCounting893.Main.nested_trailing_specialization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:29:37.588007+00:00
-- url     : https://prove2.me/submissions/1b281e3f-283e-4f66-92c9-c3ed24204eeb

import Definitions.Def_APSCounting893_Main_CoefficientLanguages

set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero {K : Type} [CommRing K] {n : ℕ} (v : Fin n) (k : ℕ) :
    coefficientIn v k (0 : MvPolynomial (Fin n) K) = 0 := by
  simp [coefficientIn]

lemma coefficientIn_monomial {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (e : Fin n →₀ ℕ) (a : K) :
    coefficientIn v k (monomial e a) =
      if e v = k then monomial (e - Finsupp.single v k) a else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, coefficientIn_zero]
  · simp [coefficientIn, support_monomial, ha]

lemma coefficientIn_add {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v k (p + q) = coefficientIn v k p + coefficientIn v k q := by
  classical
  change Finsupp.sum (AddMonoidAlgebra.coeff (p + q))
    (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0) =
    Finsupp.sum (AddMonoidAlgebra.coeff p)
      (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0) +
    Finsupp.sum (AddMonoidAlgebra.coeff q)
      (fun e a => if e v = k then monomial (e - Finsupp.single v k) a else 0)
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro e; split_ifs <;> simp
  · intro e a b; split_ifs <;> simp

lemma coefficientIn_sum {K : Type} [CommRing K] {n : ℕ} {ι : Type}
    (v : Fin n) (k : ℕ) (s : Finset ι) (p : ι → MvPolynomial (Fin n) K) :
    coefficientIn v k (∑ i ∈ s, p i) = ∑ i ∈ s, coefficientIn v k (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coefficientIn_zero]
  | @insert i s hi ih => simp [hi, coefficientIn_add, ih]

lemma coefficientIn_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) (e : Fin n →₀ ℕ) :
    (coefficientIn v k p).coeff e =
      if e v = 0 then p.coeff (e + Finsupp.single v k) else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    rw [coefficientIn_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp
  | monomial d a =>
    rw [coefficientIn_monomial]
    by_cases hd : d v = k
    · rw [if_pos hd]
      by_cases he : e v = 0
      · rw [if_pos he, coeff_monomial, coeff_monomial]
        have hle : Finsupp.single v k ≤ d := Finsupp.single_le_iff.mpr hd.ge
        have hi : d - Finsupp.single v k = e ↔ d = e + Finsupp.single v k := by
          constructor
          · intro h; rw [← h, tsub_add_cancel_of_le hle]
          · intro h; simp [h]
        simp only [hi]
      · rw [if_neg he, coeff_monomial]
        have hi : d - Finsupp.single v k ≠ e := by
          intro h
          have := congrArg (fun f : Fin n →₀ ℕ => f v) h
          simp [Finsupp.tsub_apply, hd] at this
          exact he this.symm
        simp [hi]
    · rw [if_neg hd, coeff_zero]
      split_ifs with he
      · rw [coeff_monomial]
        have hi : d ≠ e + Finsupp.single v k := by
          intro h; apply hd
          simpa [he] using congrArg (fun f : Fin n →₀ ℕ => f v) h
        simp [hi]
      · rfl

lemma coefficientIn_ne_zero_iff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k p ≠ 0 ↔ ∃ e ∈ p.support, e v = k := by
  classical
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_coeff_ne_zero h
    rw [coefficientIn_coeff] at he
    split_ifs at he with hv
    · refine ⟨e + Finsupp.single v k, mem_support_iff.mpr he, ?_⟩
      simp [hv]
    · exact (he rfl).elim
  · rintro ⟨e, he, hv⟩ h
    have ha : (e - Finsupp.single v k) v = 0 := by simp [Finsupp.tsub_apply, hv]
    have hb : e - Finsupp.single v k + Finsupp.single v k = e :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hv.ge)
    have := congrArg (coeff (e - Finsupp.single v k)) h
    simpa [coefficientIn_coeff, ha, hb, mem_support_iff.mp he] using this

lemma trailingCoefficient_ne_zero {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    trailingCoefficient v p ≠ 0 := by
  classical
  have hs : p.support.Nonempty := support_nonempty.mpr hp
  rw [trailingCoefficient, dif_pos hs, coefficientIn_ne_zero_iff]
  exact Finset.mem_image.mp (Finset.min'_mem _ (hs.image _))

lemma coefficientIn_totalDegree_le {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    (coefficientIn v k p).totalDegree ≤ p.totalDegree := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro e he
  have hc := mem_support_iff.mp he
  rw [coefficientIn_coeff] at hc
  split_ifs at hc with hv
  · have hd := le_totalDegree (mem_support_iff.mpr hc)
    have hadd : (e + Finsupp.single v k).sum (fun _ a => a) =
        e.sum (fun _ a => a) + k := by
      simp [Finsupp.sum_add_index']
    rw [hadd] at hd
    exact (Nat.le_add_right _ _).trans hd
  · exact (hc rfl).elim

lemma trailingCoefficient_totalDegree_le {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    (trailingCoefficient v p).totalDegree ≤ p.totalDegree := by
  classical
  unfold trailingCoefficient
  split_ifs
  · exact coefficientIn_totalDegree_le ..
  · simp

lemma trailingCoefficient_eq_of_min {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (k : ℕ)
    (hk : coefficientIn v k p ≠ 0)
    (hmin : ∀ j < k, coefficientIn v j p = 0) :
    trailingCoefficient v p = coefficientIn v k p := by
  classical
  obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff v k p).mp hk
  have hs : p.support.Nonempty := ⟨e, he⟩
  rw [trailingCoefficient, dif_pos hs]
  congr 1
  apply le_antisymm
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨e, he, hv⟩
  · by_contra h
    have hlt := Nat.lt_of_not_ge h
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ (hs.image (fun e => e v)))
    have hz := hmin _ hlt
    exact ((coefficientIn_ne_zero_iff v _ p).mpr ⟨d, hd, heq⟩) hz

lemma coefficientIn_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k (MvPolynomial.map f p) =
      MvPolynomial.map f (coefficientIn v k p) := by
  classical
  ext e
  simp only [coefficientIn_coeff, coeff_map]
  split_ifs <;> simp

lemma trailingCoefficient_map {K L : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (v : Fin n) (p : MvPolynomial (Fin n) K)
    (hp : MvPolynomial.map f (trailingCoefficient v p) ≠ 0) :
    trailingCoefficient v (MvPolynomial.map f p) =
      MvPolynomial.map f (trailingCoefficient v p) := by
  classical
  have hs : p.support.Nonempty := by
    by_contra h
    simp [trailingCoefficient, h] at hp
  let k := (p.support.image (fun e => e v)).min' (hs.image _)
  have htc : trailingCoefficient v p = coefficientIn v k p := by
    simp [trailingCoefficient, hs, k]
  rw [htc] at hp ⊢
  rw [← coefficientIn_map] at hp ⊢
  apply trailingCoefficient_eq_of_min v _ k hp
  intro j hj
  rw [coefficientIn_map]
  have hz : coefficientIn v j p = 0 := by
    by_contra h
    obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff v j p).mp h
    have hkj : k ≤ j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hv⟩)
    omega
  simp [hz]

lemma specializeParameters_monomial {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (e : Fin (s + (k + 1)) →₀ ℕ) (a : ℚ) :
    specializeParameters theta (monomial e a) =
      monomial (Finsupp.equivFunOnFinite.symm (fun i : Fin (k + 1) => e (i.natAdd s)))
        (algebraMap ℚ K a * ∏ i : Fin s, theta i ^ e (i.castAdd (k + 1))) := by
  classical
  simp only [specializeParameters, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    Finsupp.prod_pow]
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [monomial_eq]
  simp only [Finsupp.prod_pow, Finsupp.equivFunOnFinite_symm_apply_apply]
  simp [map_mul, map_prod, map_pow, mul_assoc]

lemma specializeParameters_coefficientIn {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (v : Fin (k + 1)) (j : ℕ)
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) :
    specializeParameters theta (coefficientIn (v.natAdd s) j p) =
      coefficientIn v j (specializeParameters theta p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [coefficientIn_add, specializeParameters, map_add] at hp hq ⊢
    rw [hp, hq]
  | monomial e a =>
    rw [coefficientIn_monomial, specializeParameters_monomial, coefficientIn_monomial]
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    split_ifs with he
    · rw [specializeParameters_monomial]
      have haux : Finsupp.equivFunOnFinite.symm
          (fun i : Fin (k + 1) => (e - Finsupp.single (v.natAdd s) j) (i.natAdd s)) =
          Finsupp.equivFunOnFinite.symm (fun i : Fin (k + 1) => e (i.natAdd s)) -
            Finsupp.single v j := by
        ext i
        simp [Finsupp.tsub_apply, Finsupp.single_apply, eq_comm]
      rw [haux]
      congr 2
      apply Finset.prod_congr rfl
      intro i _
      have hn : i.castAdd (k + 1) ≠ v.natAdd s := by
        intro h
        have hval := congrArg Fin.val h
        simp at hval
        omega
      simp [Finsupp.tsub_apply, Finsupp.single_apply, hn, Ne.symm hn]
    · simp [specializeParameters]

lemma totalDegree_eval₂_linear {K L : Type} [CommRing K] [CommRing L] {n m : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial (Fin m) L)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  simpa [Finsupp.sum_fintype] using (le_totalDegree he)

lemma specializeParameters_trailingCoefficient {K : Type} [Field K] [Algebra ℚ K]
    {s k : ℕ} (theta : Fin s → K) (v : Fin (k + 1))
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ)
    (hp : specializeParameters theta (trailingCoefficient (v.natAdd s) p) ≠ 0) :
    specializeParameters theta (trailingCoefficient (v.natAdd s) p) =
      trailingCoefficient v (specializeParameters theta p) := by
  classical
  have hs : p.support.Nonempty := by
    by_contra h
    simp [trailingCoefficient, h, specializeParameters] at hp
  let j := (p.support.image (fun e => e (v.natAdd s))).min' (hs.image _)
  have htc : trailingCoefficient (v.natAdd s) p = coefficientIn (v.natAdd s) j p := by
    simp [trailingCoefficient, hs, j]
  rw [htc, specializeParameters_coefficientIn] at hp ⊢
  symm
  apply trailingCoefficient_eq_of_min v _ j hp
  intro i hi
  rw [← specializeParameters_coefficientIn]
  have hz : coefficientIn (v.natAdd s) i p = 0 := by
    by_contra h
    obtain ⟨e, he, hv⟩ := (coefficientIn_ne_zero_iff (v.natAdd s) i p).mp h
    have hji : j ≤ i := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hv⟩)
    omega
  simp [hz, specializeParameters]

lemma specialization_nonzero_witness {s k : ℕ}
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) (hp : p ≠ 0) :
    ∃ A : MvPolynomial (Fin s) ℚ,
      A ≠ 0 ∧ A.totalDegree ≤ p.totalDegree ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        eval₂ (algebraMap ℚ K) theta A ≠ 0 → specializeParameters theta p ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : Fin (s + (k + 1)) → ℚ, eval x p ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    apply MvPolynomial.funext
    intro x
    simpa using h x
  let z : Fin (k + 1) → ℚ := fun i => x (i.natAdd s)
  let freeze : MvPolynomial (Fin (s + (k + 1))) ℚ →+* MvPolynomial (Fin s) ℚ :=
    eval₂Hom C (Fin.addCases X (fun i => C (z i)))
  have commute (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K) :
      (eval₂Hom (algebraMap ℚ K) theta).comp freeze =
        (eval₂Hom (RingHom.id K) (fun i => algebraMap ℚ K (z i))).comp
          (eval₂Hom (C.comp (algebraMap ℚ K)) (Fin.addCases (fun i => C (theta i)) X)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [freeze]
    · intro i
      refine Fin.addCases ?_ ?_ i
      · intro j; simp [freeze]
      · intro j; simp [freeze]
  refine ⟨freeze p, ?_, ?_, ?_⟩
  · intro h
    have hcomp : (eval₂Hom (RingHom.id ℚ) (fun i => x (i.castAdd (k + 1)))).comp freeze =
        eval₂Hom (RingHom.id ℚ) x := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [freeze]
      · intro i
        refine Fin.addCases ?_ ?_ i
        · intro j; simp [freeze]
        · intro j; simp [freeze, z]
    apply hx
    change (eval₂Hom (RingHom.id ℚ) x) p = 0
    rw [← hcomp, RingHom.comp_apply, h, map_zero]
  · apply totalDegree_eval₂_linear (RingHom.id ℚ)
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp
    · intro j; simp
  · intro K _ _ theta hA hz
    apply hA
    change (eval₂Hom (algebraMap ℚ K) theta) (freeze p) = 0
    rw [← RingHom.comp_apply, commute K theta, RingHom.comp_apply]
    change (eval₂Hom (RingHom.id K) (fun i => algebraMap ℚ K (z i)))
      (specializeParameters theta p) = 0
    rw [hz, map_zero]

lemma nestedTrailing_specialization_aux {s k : ℕ}
    (order : List (Fin (k + 1)))
    (p : MvPolynomial (Fin (s + (k + 1))) ℚ) (hp : p ≠ 0) :
    ∃ A : Fin order.length → MvPolynomial (Fin s) ℚ,
      (∀ i, A i ≠ 0 ∧ (A i).totalDegree ≤ p.totalDegree) ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        (∀ i, eval₂ (algebraMap ℚ K) theta (A i) ≠ 0) →
        specializeParameters theta (nestedTrailing (order.map (Fin.natAdd s)) p) =
          nestedTrailing order (specializeParameters theta p) := by
  classical
  induction order generalizing p with
  | nil =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · intro K _ _ theta h
      rfl
  | cons v order ih =>
    let q := trailingCoefficient (v.natAdd s) p
    have hq : q ≠ 0 := trailingCoefficient_ne_zero _ _ hp
    obtain ⟨a, ha, had, haw⟩ := specialization_nonzero_witness q hq
    obtain ⟨B, hB, hBw⟩ := ih q hq
    refine ⟨Fin.cons a B, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using And.intro ha (had.trans (trailingCoefficient_totalDegree_le _ _))
      · simpa using And.intro (hB j).1
          ((hB j).2.trans (trailingCoefficient_totalDegree_le _ _))
    · intro K _ _ theta hA
      have hqa : specializeParameters theta q ≠ 0 := haw K theta (by simpa using hA 0)
      have htc := specializeParameters_trailingCoefficient theta v p hqa
      have htail : ∀ i, eval₂ (algebraMap ℚ K) theta (B i) ≠ 0 := by
        intro i; simpa using hA i.succ
      have hrec := hBw K theta htail
      change specializeParameters theta (nestedTrailing (order.map (Fin.natAdd s)) q) =
        nestedTrailing order (trailingCoefficient v (specializeParameters theta p))
      rw [← htc]
      exact hrec

end APSCounting893.Main

open APSCounting893.Main

theorem solution (s k D : ℕ) (R : MvPolynomial (Fin (s + (k + 1))) ℚ)
    (hR : R ≠ 0) (hdegree : R.totalDegree ≤ D) :
    ∃ A : Fin k → MvPolynomial (Fin s) ℚ,
      (∀ i, A i ≠ 0 ∧ (A i).totalDegree ≤ D) ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        (∀ i, MvPolynomial.eval₂ (algebraMap ℚ K) theta (A i) ≠ 0) →
        specializeParameters theta
          (nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc.natAdd s)) R) =
          nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc)) (specializeParameters theta R) := by
  have h : ∃ A : Fin k → MvPolynomial (Fin s) ℚ,
      (∀ i, A i ≠ 0 ∧ (A i).totalDegree ≤ R.totalDegree) ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        (∀ i, MvPolynomial.eval₂ (algebraMap ℚ K) theta (A i) ≠ 0) →
        specializeParameters theta
          (nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc.natAdd s)) R) =
          nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc)) (specializeParameters theta R) := by
    have haux := nestedTrailing_specialization_aux (s := s)
      (List.ofFn (fun i : Fin k => i.castSucc)) R hR
    rw [List.length_ofFn] at haux
    simpa only [List.map_ofFn, Function.comp_def] using haux
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, fun i => ⟨(hA i).1, (hA i).2.trans hdegree⟩, hc⟩

