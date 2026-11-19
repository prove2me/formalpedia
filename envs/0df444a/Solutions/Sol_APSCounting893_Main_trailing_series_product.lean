-- Prove2me | solution 1 for APSCounting893.Main.trailing_series_product
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:08:36.920198+00:00
-- url     : https://prove2.me/submissions/8952ad49-ec6c-4fae-b02c-a218befc25c6

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Mathlib
import Mathlib.RingTheory.HahnSeries.PowerSeries
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0

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
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def splitVariable {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) : Polynomial (MvPolynomial (Fin n) K) :=
  ∑ e ∈ p.support, Polynomial.monomial (e v) (MvPolynomial.monomial (e.erase v) (p.coeff e))

lemma splitVariable_zero {K : Type} [CommRing K] {n : ℕ} (v : Fin n) :
    splitVariable v (0 : MvPolynomial (Fin n) K) = 0 := by simp [splitVariable]

lemma splitVariable_monomial {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (e : Fin n →₀ ℕ) (a : K) :
    splitVariable v (monomial e a) = Polynomial.monomial (e v) (monomial (e.erase v) a) := by
  classical
  by_cases ha : a = 0
  · simp [ha, splitVariable_zero]
  · simp [splitVariable, support_monomial, ha]

lemma splitVariable_add {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    splitVariable v (p + q) = splitVariable v p + splitVariable v q := by
  classical
  change Finsupp.sum (AddMonoidAlgebra.coeff (p + q))
    (fun e a => Polynomial.monomial (e v) (monomial (e.erase v) a)) =
      Finsupp.sum (AddMonoidAlgebra.coeff p) (fun e a => Polynomial.monomial (e v) (monomial (e.erase v) a)) +
      Finsupp.sum (AddMonoidAlgebra.coeff q) (fun e a => Polynomial.monomial (e v) (monomial (e.erase v) a))
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro e; simp
  · intro e a b; simp

lemma splitVariable_mul {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    splitVariable v (p * q) = splitVariable v p * splitVariable v q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [add_mul, splitVariable_add, hp, hr]
  | monomial e a =>
    induction q using MvPolynomial.induction_on' with
    | add q r hq hr => simp only [mul_add, splitVariable_add, hq, hr]
    | monomial f b =>
      rw [monomial_mul, splitVariable_monomial, splitVariable_monomial, splitVariable_monomial,
        Polynomial.monomial_mul_monomial, monomial_mul]
      simp only [Finsupp.add_apply, Finsupp.erase_add]

lemma splitVariable_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (k : ℕ) :
    (splitVariable v p).coeff k = coefficientIn v k p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [splitVariable_add, Polynomial.coeff_add, hp, hq, coefficientIn_add]
  | monomial e a =>
    rw [splitVariable_monomial, Polynomial.coeff_monomial, coefficientIn_monomial]
    have he : e.erase v = e - Finsupp.single v (e v) := by
      ext i
      by_cases hi : i = v
      · subst i; simp
      · simp [hi]
    split_ifs with h
    · rw [h] at he
      rw [he]
    · rfl

lemma splitVariable_eval {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    Polynomial.eval (X v) (splitVariable v p) = p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [splitVariable_add, Polynomial.eval_add, hp, hq]
  | monomial e a =>
    rw [splitVariable_monomial, Polynomial.eval_monomial]
    rw [X_pow_eq_monomial, monomial_mul, mul_one]
    rw [Finsupp.erase_add_single]

lemma splitVariable_ne_zero {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) : splitVariable v p ≠ 0 := by
  intro h
  have hh := splitVariable_eval v p
  rw [h, Polynomial.eval_zero] at hh
  exact hp hh.symm

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def nonnegativeHahnRing (K : Type) [Field K] : ValuationSubring (HahnSeries ℚ K) :=
  (AddValuation.toValuation (HahnSeries.addVal ℚ K)).valuationSubring

lemma hahn_coeff_zero_mul_nonnegative {K : Type} [Field K] (x y : HahnSeries ℚ K)
    (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hxo : 0 ≤ x.order := HahnSeries.zero_le_orderTop_iff.mp hx
  have hyo : 0 ≤ y.order := HahnSeries.zero_le_orderTop_iff.mp hy
  by_cases hxord : x.order = 0
  · by_cases hyord : y.order = 0
    · simpa only [HahnSeries.leadingCoeff_eq, hxord, hyord, add_zero] using HahnSeries.coeff_mul_order_add_order x y
    · have hpos : 0 < y.order := lt_of_le_of_ne hyo (Ne.symm hyord)
      rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, mul_zero]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [HahnSeries.order_mul hx0 hy0, hxord, zero_add]
      exact hpos
  · have hpos : 0 < x.order := lt_of_le_of_ne hxo (Ne.symm hxord)
    rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, zero_mul]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul hx0 hy0]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right hyo)

noncomputable def hahnResidueHom (K : Type) [Field K] : nonnegativeHahnRing K →+* K where
  toFun x := x.val.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := hahn_coeff_zero_mul_nonnegative x.val y.val x.property y.property

noncomputable def hahnConstantLift (K : Type) [Field K] : K →+* nonnegativeHahnRing K where
  toFun c := ⟨HahnSeries.C c, by
    change 0 ≤ (HahnSeries.C c : HahnSeries ℚ K).orderTop
    rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.order_C]⟩
  map_zero' := Subtype.ext HahnSeries.C.map_zero
  map_one' := Subtype.ext HahnSeries.C.map_one
  map_add' a b := Subtype.ext (HahnSeries.C.map_add a b)
  map_mul' a b := Subtype.ext (HahnSeries.C.map_mul a b)

lemma hahnResidue_constant {K : Type} [Field K] (c : K) :
    hahnResidueHom K (hahnConstantLift K c) = c := by simp [hahnResidueHom, hahnConstantLift]

lemma hahnResidue_single_one {K : Type} [Field K] :
    ∃ x : nonnegativeHahnRing K, x.val = HahnSeries.single (1 : ℚ) (1 : K) ∧ hahnResidueHom K x = 0 := by
  refine ⟨⟨HahnSeries.single (1 : ℚ) (1 : K), ?_⟩, rfl, ?_⟩
  · change 0 ≤ (HahnSeries.single (1 : ℚ) (1 : K)).orderTop
    rw [HahnSeries.orderTop_single]
    · norm_num
    · exact one_ne_zero
  · simp [hahnResidueHom, HahnSeries.coeff_single_of_ne]

end APSCounting893.Main
end Component_2

section Component_3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def hahnCoefficientMap {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) : HahnSeries ℚ R →+* HahnSeries ℚ S where
  toFun x := x.map f
  map_zero' := by ext q; simp
  map_one' := by ext q; simp only [HahnSeries.map_coeff, HahnSeries.coeff_one]; split_ifs <;> simp
  map_add' x y := by ext q; simp
  map_mul' x y := HahnSeries.map_mul f.toNonUnitalRingHom

lemma hahnCoefficientMap_coeff {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (x : HahnSeries ℚ R) (q : ℚ) :
    (hahnCoefficientMap f x).coeff q = f (x.coeff q) := rfl

lemma hahnCoefficientMap_single {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (q : ℚ) (r : R) :
    hahnCoefficientMap f (HahnSeries.single q r) = HahnSeries.single q (f r) := by
  ext t
  simp only [hahnCoefficientMap_coeff, HahnSeries.coeff_single]
  split_ifs <;> simp

lemma hahnCoefficientMap_regular {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (x : HahnSeries ℚ R) (hx : 0 ≤ x.orderTop) :
    0 ≤ (hahnCoefficientMap f x).orderTop := by
  apply HahnSeries.le_orderTop_iff_forall.mpr
  intro q hq
  rw [hahnCoefficientMap_coeff, HahnSeries.coeff_eq_zero_of_lt_orderTop (hq.trans_le hx), map_zero]

noncomputable def polynomialToHahn {K : Type} [CommRing K] :
    Polynomial (HahnSeries ℚ K) →+* HahnSeries ℚ (Polynomial K) :=
  Polynomial.eval₂RingHom (hahnCoefficientMap Polynomial.C) (HahnSeries.C Polynomial.X)

lemma polynomialToHahn_C {K : Type} [CommRing K] (x : HahnSeries ℚ K) :
    polynomialToHahn (Polynomial.C x) = hahnCoefficientMap Polynomial.C x := by
  simp [polynomialToHahn]

lemma polynomialToHahn_X {K : Type} [CommRing K] :
    polynomialToHahn (Polynomial.X : Polynomial (HahnSeries ℚ K)) = HahnSeries.C Polynomial.X := by
  simp [polynomialToHahn]

lemma polynomialToHahn_linear {K : Type} [CommRing K] (x : HahnSeries ℚ K) :
    polynomialToHahn (Polynomial.X - Polynomial.C x) =
      HahnSeries.C Polynomial.X - hahnCoefficientMap Polynomial.C x := by
  rw [map_sub, polynomialToHahn_X, polynomialToHahn_C]

lemma hahn_coeff_zero_mul_regular {R : Type} [CommRing R] [IsDomain R]
    (x y : HahnSeries ℚ R) (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    (x*y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hy0 : y = 0
  · simp [hy0]
  have hxo : 0 ≤ x.order := HahnSeries.zero_le_orderTop_iff.mp hx
  have hyo : 0 ≤ y.order := HahnSeries.zero_le_orderTop_iff.mp hy
  by_cases hxord : x.order = 0
  · by_cases hyord : y.order = 0
    · simpa only [HahnSeries.leadingCoeff_eq, hxord, hyord, add_zero] using HahnSeries.coeff_mul_order_add_order x y
    · have hpos : 0 < y.order := lt_of_le_of_ne hyo (Ne.symm hyord)
      rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, mul_zero]
      apply HahnSeries.coeff_eq_zero_of_lt_order
      rw [HahnSeries.order_mul hx0 hy0, hxord, zero_add]
      exact hpos
  · have hpos : 0 < x.order := lt_of_le_of_ne hxo (Ne.symm hxord)
    rw [HahnSeries.coeff_eq_zero_of_lt_order hpos, zero_mul]
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul hx0 hy0]
    exact lt_of_lt_of_le hpos (le_add_of_nonneg_right hyo)

end APSCounting893.Main
end Component_3

section Component_4

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma hahn_regular_mul {R : Type} [CommRing R] [IsDomain R]
    {x y : HahnSeries ℚ R} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    0 ≤ (x*y).orderTop := by
  rw [HahnSeries.orderTop_mul]
  exact add_nonneg hx hy

lemma hahn_regular_pow {R : Type} [CommRing R] [IsDomain R]
    {x : HahnSeries ℚ R} (hx : 0 ≤ x.orderTop) (n : ℕ) : 0 ≤ (x^n).orderTop := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact hahn_regular_mul ih hx

lemma hahn_coeff_zero_pow_regular {R : Type} [CommRing R] [IsDomain R]
    {x : HahnSeries ℚ R} (hx : 0 ≤ x.orderTop) (n : ℕ) :
    (x^n).coeff 0 = x.coeff 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hahn_coeff_zero_mul_regular _ _ (hahn_regular_pow hx n) hx, ih, pow_succ]

lemma hahn_regular_prod {R ι : Type} [CommRing R] [IsDomain R]
    (s : Finset ι) (x : ι → HahnSeries ℚ R) (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    0 ≤ (∏ i ∈ s, x i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hahn_regular_mul (hx a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hx i (Finset.mem_insert_of_mem hi)))

lemma hahn_coeff_zero_prod_regular {R ι : Type} [CommRing R] [IsDomain R]
    (s : Finset ι) (x : ι → HahnSeries ℚ R) (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (∏ i ∈ s, x i).coeff 0 = ∏ i ∈ s, (x i).coeff 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      hahn_coeff_zero_mul_regular _ _ (hx a (Finset.mem_insert_self _ _))
        (hahn_regular_prod s x (fun i hi => hx i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))]

lemma polynomialToHahn_linear_regular {K : Type} [Field K]
    (x : HahnSeries ℚ K) (hx : 0 ≤ x.orderTop) :
    0 ≤ (polynomialToHahn (Polynomial.X - Polynomial.C x)).orderTop := by
  rw [polynomialToHahn_linear]
  apply le_trans _ HahnSeries.min_orderTop_le_orderTop_sub
  apply le_min
  · rw [HahnSeries.zero_le_orderTop_iff, HahnSeries.order_C]
  · exact hahnCoefficientMap_regular Polynomial.C x hx

lemma polynomialToHahn_linear_coeff_zero {K : Type} [Field K]
    (x : HahnSeries ℚ K) :
    (polynomialToHahn (Polynomial.X - Polynomial.C x)).coeff 0 =
      Polynomial.X - Polynomial.C (x.coeff 0) := by
  rw [polynomialToHahn_linear, HahnSeries.coeff_sub, hahnCoefficientMap_coeff]
  simp [HahnSeries.C_apply]

lemma polynomialToHahn_product_linear_coeff_zero {K ι : Type} [Field K]
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (polynomialToHahn (∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i)).coeff 0 =
      ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  rw [map_prod]
  simp only [map_pow]
  rw [hahn_coeff_zero_prod_regular s _ (fun i hi =>
    hahn_regular_pow (polynomialToHahn_linear_regular _ (hx i hi)) _)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hahn_coeff_zero_pow_regular (polynomialToHahn_linear_regular _ (hx i hi)),
    polynomialToHahn_linear_coeff_zero]

end APSCounting893.Main
end Component_4

section Component_5

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma polynomial_hahn_orderTop {R : Type} [CommRing R]
    (p : Polynomial R) (hp : p ≠ 0) :
    (algebraMap (Polynomial R) (HahnSeries ℚ R) p).orderTop = (p.natTrailingDegree : ℚ) := by
  let f := HahnSeries.toPowerSeries.symm (p : PowerSeries R)
  have hnat : f.orderTop = (p.natTrailingDegree : WithTop ℕ) := by
    apply HahnSeries.orderTop_eq_of_le
    · change PowerSeries.coeff p.natTrailingDegree (p : PowerSeries R) ≠ 0
      simpa using (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp)
    · intro j hj
      apply Polynomial.natTrailingDegree_le_of_ne_zero
      change PowerSeries.coeff j (p : PowerSeries R) ≠ 0 at hj
      simpa using hj
  change (HahnSeries.embDomain (Nat.castOrderEmbedding (α := ℚ)) f).orderTop = _
  rw [HahnSeries.orderTop_embDomain, hnat]
  rfl

lemma polynomial_hahn_coeff_nat {R : Type} [CommRing R] (p : Polynomial R) (n : ℕ) :
    (algebraMap (Polynomial R) (HahnSeries ℚ R) p).coeff (n : ℚ) = p.coeff n := by
  rw [Polynomial.algebraMap_hahnSeries_apply, HahnSeries.ofPowerSeries_apply_coeff]
  simp

lemma polynomial_hahn_leadingCoeff {R : Type} [CommRing R] (p : Polynomial R) :
    (algebraMap (Polynomial R) (HahnSeries ℚ R) p).leadingCoeff = p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_zero]
  have hh := polynomial_hahn_orderTop p hp
  have ho : (algebraMap (Polynomial R) (HahnSeries ℚ R) p).order = (p.natTrailingDegree : ℚ) := by
    have hp' : algebraMap (Polynomial R) (HahnSeries ℚ R) p ≠ 0 := by
      intro hz
      apply hp
      exact (Polynomial.algebraMap_hahnSeries_injective (Γ := ℚ) (R := R)) (by simpa only [map_zero] using hz)
    rw [HahnSeries.orderTop_of_ne_zero hp'] at hh
    rw [HahnSeries.order_of_ne hp']
    exact WithTop.coe_inj.mp hh
  rw [HahnSeries.leadingCoeff_eq, ho, polynomial_hahn_coeff_nat]
  rfl

end APSCounting893.Main
end Component_5

section Component_6

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma hahnCoefficientMap_order {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (x : HahnSeries ℚ R) :
    (hahnCoefficientMap f x).order = x.order := by
  by_cases hx : x = 0
  · simp [hx, map_zero]
  have hxn : x.coeff x.order ≠ 0 := by
    simpa only [← HahnSeries.leadingCoeff_eq] using (HahnSeries.leadingCoeff_ne_zero.mpr hx)
  have hyn : (hahnCoefficientMap f x).coeff x.order ≠ 0 := by
    rw [hahnCoefficientMap_coeff]
    exact fun h => hxn (hf (h.trans f.map_zero.symm))
  have hy : hahnCoefficientMap f x ≠ 0 := fun h => hyn (by simp [h])
  have ho : (hahnCoefficientMap f x).orderTop = (x.order : WithTop ℚ) := by
    apply HahnSeries.orderTop_eq_of_le hyn
    intro q hq
    apply HahnSeries.order_le_of_coeff_ne_zero
    exact fun h => hq (by rw [hahnCoefficientMap_coeff, h, map_zero])
  rw [HahnSeries.orderTop_of_ne_zero hy] at ho
  rw [HahnSeries.order_of_ne hy]
  exact WithTop.coe_inj.mp ho

lemma hahnCoefficientMap_leadingCoeff {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (x : HahnSeries ℚ R) :
    (hahnCoefficientMap f x).leadingCoeff = f x.leadingCoeff := by
  rw [HahnSeries.leadingCoeff_eq, hahnCoefficientMap_order f hf,
    hahnCoefficientMap_coeff, HahnSeries.leadingCoeff_eq]

lemma polynomialToHahn_product_linear_leadingCoeff {K ι : Type} [Field K]
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (polynomialToHahn (∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i)).leadingCoeff =
      ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  let p := ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i
  have hreg : 0 ≤ (polynomialToHahn p).orderTop := by
    dsimp only [p]
    rw [map_prod]
    simp only [map_pow]
    exact hahn_regular_prod s _ (fun i hi => hahn_regular_pow (polynomialToHahn_linear_regular _ (hx i hi)) _)
  have hres := polynomialToHahn_product_linear_coeff_zero s x mu hx
  have hn : (polynomialToHahn p).coeff 0 ≠ 0 := by
    rw [hres]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (Polynomial.monic_X_sub_C _).ne_zero
  have ho : (polynomialToHahn p).order = 0 := by
    exact le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hn)
      (HahnSeries.zero_le_orderTop_iff.mp hreg)
  rw [HahnSeries.leadingCoeff_eq, ho]
  exact hres

lemma polynomialToHahn_scalar_product_leadingCoeff {K ι : Type} [Field K]
    (c : HahnSeries ℚ K) (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop) :
    (polynomialToHahn (Polynomial.C c * ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i)).leadingCoeff =
      Polynomial.C c.leadingCoeff * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  rw [map_mul, polynomialToHahn_C, HahnSeries.leadingCoeff_mul,
    hahnCoefficientMap_leadingCoeff Polynomial.C Polynomial.C_injective,
    polynomialToHahn_product_linear_leadingCoeff s x mu hx]

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def splitBivariate {K : Type} [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun j => if j = 0 then Polynomial.X else Polynomial.C Polynomial.X)

noncomputable def bivariateOther {K : Type} [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = 0 then 0 else Polynomial.X)

lemma splitBivariate_monomial {K : Type} [CommRing K] (e : Fin 2 →₀ ℕ) (a : K) :
    splitBivariate (monomial e a) = Polynomial.monomial (e 0) (Polynomial.monomial (e 1) a) := by
  change MvPolynomial.eval₂ _ _ (monomial e a) = _
  rw [MvPolynomial.eval₂_monomial, e.prod_fintype _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [RingHom.comp_apply, ite_true, ite_false, one_ne_zero]
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_mul, map_pow]
  ring

lemma bivariateOther_monomial {K : Type} [CommRing K] (e : Fin 2 →₀ ℕ) (a : K) :
    bivariateOther (monomial e a) = if e 0 = 0 then Polynomial.monomial (e 1) a else 0 := by
  change MvPolynomial.eval₂ _ _ (monomial e a) = _
  rw [MvPolynomial.eval₂_monomial, e.prod_fintype _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [ite_true, ite_false, one_ne_zero]
  by_cases h : e 0 = 0
  · simp only [h, pow_zero, one_mul, ite_true]
    exact Polynomial.C_mul_X_pow_eq_monomial
  · simp [h, zero_pow h]

lemma splitBivariate_coeff {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) (k : ℕ) :
    (splitBivariate p).coeff k = bivariateOther (coefficientIn 0 k p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, coefficientIn_add, map_add, hp, hq]
  | monomial e a =>
    rw [splitBivariate_monomial, Polynomial.coeff_monomial, coefficientIn_monomial]
    by_cases h : e 0 = k
    · simp [h, bivariateOther_monomial, Finsupp.tsub_apply, Finsupp.single_apply]
    · simp only [h, Ne.symm h, ite_false, map_zero]

noncomputable def unsplitBivariate {K : Type} [CommRing K] :
    Polynomial (Polynomial K) →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 1)) (MvPolynomial.X 0)

lemma unsplit_splitBivariate {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    unsplitBivariate (splitBivariate p) = p := by
  have hh : (unsplitBivariate (K := K)).comp splitBivariate = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [unsplitBivariate, splitBivariate]
    · intro j
      fin_cases j <;> simp [unsplitBivariate, splitBivariate]
  exact RingHom.congr_fun hh p

lemma splitBivariate_injective {K : Type} [CommRing K] :
    Function.Injective (splitBivariate (K := K)) := by
  intro p q hpq
  rw [← unsplit_splitBivariate p, ← unsplit_splitBivariate q, hpq]

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma trailingCoefficient_eq_split {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    trailingCoefficient v p = (splitVariable v p).trailingCoeff := by
  classical
  by_cases hp : p = 0
  · subst p
    simp [trailingCoefficient, splitVariable_zero]
  · have hsplit := splitVariable_ne_zero v p hp
    rw [Polynomial.trailingCoeff]
    rw [splitVariable_coeff]
    apply trailingCoefficient_eq_of_min
    · rw [← splitVariable_coeff]
      exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hsplit
    · intro j hj
      rw [← splitVariable_coeff]
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj

lemma trailingCoefficient_mul {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    trailingCoefficient v (p * q) = trailingCoefficient v p * trailingCoefficient v q := by
  rw [trailingCoefficient_eq_split, splitVariable_mul, Polynomial.trailingCoeff_mul,
    ← trailingCoefficient_eq_split, ← trailingCoefficient_eq_split]

lemma splitVariable_C {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (a : K) : splitVariable v (C a) = Polynomial.C (C a) := by
  change splitVariable v (monomial 0 a) = _
  rw [splitVariable_monomial]
  simp

lemma trailingCoefficient_C {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (a : K) : trailingCoefficient v (C a) = C a := by
  rw [trailingCoefficient_eq_split, splitVariable_C]
  simp [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_C]

noncomputable def trailingCoefficientHom {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    (v : Fin n) : MvPolynomial (Fin n) K →* MvPolynomial (Fin n) K where
  toFun := trailingCoefficient v
  map_one' := by simpa using trailingCoefficient_C v (1 : K)
  map_mul' := trailingCoefficient_mul v

lemma trailingCoefficient_pow {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (m : ℕ) :
    trailingCoefficient v (p ^ m) = trailingCoefficient v p ^ m :=
  (trailingCoefficientHom v).map_pow p m

lemma trailingCoefficient_prod {K : Type} [CommRing K] [NoZeroDivisors K] {n : ℕ}
    {ι : Type} (v : Fin n) (s : Finset ι) (p : ι → MvPolynomial (Fin n) K) :
    trailingCoefficient v (∏ i ∈ s, p i) = ∏ i ∈ s, trailingCoefficient v (p i) :=
  map_prod (trailingCoefficientHom v) p s

end APSCounting893.Main
end Component_8

section Component_9

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero_mul {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v 0 (p * q) = coefficientIn v 0 p * coefficientIn v 0 q := by
  rw [← splitVariable_coeff, splitVariable_mul, Polynomial.mul_coeff_zero,
    splitVariable_coeff, splitVariable_coeff]

lemma coefficientIn_zero_C {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (a : K) : coefficientIn v 0 (C a) = C a := by
  rw [← splitVariable_coeff, splitVariable_C, Polynomial.coeff_C_zero]

lemma coefficientIn_neg {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v k (-p) = -coefficientIn v k p := by
  classical
  ext e
  simp only [coefficientIn_coeff, coeff_neg]
  split_ifs <;> simp

lemma coefficientIn_sub {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p q : MvPolynomial (Fin n) K) :
    coefficientIn v k (p - q) = coefficientIn v k p - coefficientIn v k q := by
  rw [sub_eq_add_neg, coefficientIn_add, coefficientIn_neg, sub_eq_add_neg]

lemma coefficientIn_zero_X {K : Type} [CommRing K] {n : ℕ}
    (v j : Fin n) : coefficientIn v 0 (X j : MvPolynomial (Fin n) K) =
      if j = v then 0 else X j := by
  classical
  change coefficientIn v 0 (monomial (Finsupp.single j 1) (1 : K)) = _
  rw [coefficientIn_monomial]
  by_cases hj : j = v
  · subst j; simp
  · simp [Finsupp.single_apply, hj, Ne.symm hj]
    rfl

lemma coefficientIn_zero_pow {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (m : ℕ) :
    coefficientIn v 0 (p ^ m) = coefficientIn v 0 p ^ m := by
  induction m with
  | zero => simpa using coefficientIn_zero_C v (1 : K)
  | succ m ih => rw [pow_succ, coefficientIn_zero_mul, ih, pow_succ]

lemma trailingCoefficient_eq_of_zero_coeff {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) (hp : coefficientIn v 0 p ≠ 0) :
    trailingCoefficient v p = coefficientIn v 0 p :=
  trailingCoefficient_eq_of_min v p 0 hp (fun j hj => False.elim (Nat.not_lt_zero j hj))

end APSCounting893.Main
end Component_9

section Component_10

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def coefficientZeroHom {K : Type} [CommRing K] {n : ℕ} (v : Fin n) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K where
  toFun := coefficientIn v 0
  map_zero' := coefficientIn_zero _ _
  map_one' := coefficientIn_zero_C v 1
  map_add' := coefficientIn_add v 0
  map_mul' := coefficientIn_zero_mul v

lemma bivariateOther_recover {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 1) (bivariateOther p) = coefficientIn 0 0 p := by
  have hh : (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (1 : Fin 2))).comp bivariateOther =
      coefficientZeroHom (K := K) 0 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, bivariateOther, MvPolynomial.eval₂Hom_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (coefficientIn_zero_C _ _).symm
    · intro j
      fin_cases j <;> simp [bivariateOther, coefficientZeroHom, coefficientIn_zero_X]
  exact RingHom.congr_fun hh p

lemma coefficientIn_zero_idempotent {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) :
    coefficientIn v 0 (coefficientIn v k p) = coefficientIn v k p := by
  ext e
  simp only [coefficientIn_coeff, Finsupp.single_zero, add_zero]
  split_ifs <;> rfl

lemma bivariateOther_coefficient_ne_zero {K : Type} [CommRing K]
    (k : ℕ) (p : MvPolynomial (Fin 2) K) (hp : coefficientIn 0 k p ≠ 0) :
    bivariateOther (coefficientIn 0 k p) ≠ 0 := by
  intro hz
  have hh := bivariateOther_recover (coefficientIn 0 k p)
  rw [hz, Polynomial.eval₂_zero, coefficientIn_zero_idempotent] at hh
  exact hp hh.symm

lemma bivariate_trailingCoeff {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    (splitBivariate p).trailingCoeff = bivariateOther (trailingCoefficient 0 p) := by
  classical
  by_cases hp : p = 0
  · simp [hp, trailingCoefficient]
  have hs : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp
  let k := (p.support.image (fun e => e 0)).min' (hs.image _)
  have hcoef : coefficientIn 0 k p ≠ 0 := by
    apply (coefficientIn_ne_zero_iff 0 k p).mpr
    exact Finset.mem_image.mp (Finset.min'_mem _ (hs.image _))
  have hsplit : splitBivariate p ≠ 0 := fun hz => hp (splitBivariate_injective (by simpa using hz))
  have hcoeff : (splitBivariate p).coeff k ≠ 0 := by
    rw [splitBivariate_coeff]
    exact bivariateOther_coefficient_ne_zero k p hcoef
  have hlower : ∀ j < k, (splitBivariate p).coeff j = 0 := by
    intro j hj
    rw [splitBivariate_coeff]
    have hz : coefficientIn 0 j p = 0 := by
      by_contra hn
      obtain ⟨e, he, hev⟩ := (coefficientIn_ne_zero_iff 0 j p).mp hn
      have hkj : k ≤ j := Finset.min'_le _ _ (Finset.mem_image.mpr ⟨e, he, hev⟩)
      omega
    rw [hz, map_zero]
  have hdeg : (splitBivariate p).natTrailingDegree = k :=
    le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hcoeff)
      (Polynomial.le_natTrailingDegree hsplit hlower)
  rw [Polynomial.trailingCoeff, hdeg, splitBivariate_coeff]
  rw [trailingCoefficient, dif_pos hs]

end APSCounting893.Main
end Component_10

section Component_11

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def bivariateSeries {K : Type} [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial (HahnSeries ℚ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp HahnSeries.C)
    (fun j => if j = 0 then Polynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) else Polynomial.X)

lemma bivariateSeries_X_zero {K : Type} [CommRing K] :
    bivariateSeries (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) =
      Polynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) := by simp [bivariateSeries]

lemma bivariateSeries_X_one {K : Type} [CommRing K] :
    bivariateSeries (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.X := by simp [bivariateSeries]

lemma splitBivariate_X_zero {K : Type} [CommRing K] :
    splitBivariate (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.X := by simp [splitBivariate]

lemma splitBivariate_X_one {K : Type} [CommRing K] :
    splitBivariate (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.C Polynomial.X := by simp [splitBivariate]

lemma polynomialToHahn_bivariateSeries {K : Type} [CommRing K] (p : MvPolynomial (Fin 2) K) :
    polynomialToHahn (bivariateSeries p) =
      algebraMap (Polynomial (Polynomial K)) (HahnSeries ℚ (Polynomial K)) (splitBivariate p) := by
  have hh : (polynomialToHahn (K := K)).comp bivariateSeries =
      (algebraMap (Polynomial (Polynomial K)) (HahnSeries ℚ (Polynomial K))).comp splitBivariate := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, bivariateSeries, splitBivariate, MvPolynomial.eval₂Hom_C,
        RingHom.comp_apply, polynomialToHahn_C]
      rw [show HahnSeries.C c = HahnSeries.single (0 : ℚ) c from rfl, hahnCoefficientMap_single]
      simp [Polynomial.algebraMap_hahnSeries_apply]
    · intro j
      fin_cases j <;> ext q <;>
        simp [bivariateSeries, splitBivariate, polynomialToHahn, hahnCoefficientMap,
          Polynomial.algebraMap_hahnSeries_apply, HahnSeries.C_apply, HahnSeries.coeff_single]

  exact RingHom.congr_fun hh p

lemma bivariate_scalar_product_trailingCoeff {K ι : Type} [Field K]
    (p : MvPolynomial (Fin 2) K) (c : HahnSeries ℚ K) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : bivariateSeries p = Polynomial.C c *
      ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : K, a ≠ 0 ∧ (splitBivariate p).trailingCoeff =
      Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  refine ⟨c.leadingCoeff, HahnSeries.leadingCoeff_ne_zero.mpr hc, ?_⟩
  have hh := congrArg (fun q => (polynomialToHahn q).leadingCoeff) hp
  rw [polynomialToHahn_bivariateSeries, polynomial_hahn_leadingCoeff,
    polynomialToHahn_scalar_product_leadingCoeff c s x mu hx] at hh
  exact hh

end APSCounting893.Main
end Component_11

section Component_12

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma bivariate_trailing_factorization {K ι : Type} [Field K]
    (p : MvPolynomial (Fin 2) K) (c : HahnSeries ℚ K) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → HahnSeries ℚ K) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : bivariateSeries p = Polynomial.C c *
      ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : K, a ≠ 0 ∧ bivariateOther (trailingCoefficient 0 p) =
      Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  obtain ⟨a, ha, heq⟩ := bivariate_scalar_product_trailingCoeff p c hc s x mu hx hp
  rw [bivariate_trailingCoeff] at heq
  exact ⟨a, ha, heq⟩

end APSCounting893.Main
end Component_12

open APSCounting893.Main
theorem solution
    {ι : Type} (p : MvPolynomial (Fin 2) ℂ) (c : PuiseuxAmbient) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → PuiseuxAmbient) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : MvPolynomial.eval₂Hom (Polynomial.C.comp HahnSeries.C)
      (fun j : Fin 2 => if j = 0 then Polynomial.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else Polynomial.X) p =
        Polynomial.C c * ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : ℂ, a ≠ 0 ∧ MvPolynomial.eval₂Hom Polynomial.C
      (fun j : Fin 2 => if j = 0 then 0 else Polynomial.X) (trailingCoefficient 0 p) =
        Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  exact bivariate_trailing_factorization p c hc s x mu hx hp
