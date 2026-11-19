-- Prove2me | solution 1 for APSCounting893.Main.resultant_criterion_for_aps
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:08:37.328358+00:00
-- url     : https://prove2.me/submissions/a5754b77-d8f9-442f-9320-28c723149345

import Definitions.Def_APSCounting893_Main_CoefficientLanguages
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Theorems.Thm_APSCounting893_Main_affine_perturbation_residue_coverage
import Theorems.Thm_APSCounting893_Main_ierardi_resultant_factorization
import Theorems.Thm_APSCounting893_Main_trailing_series_product
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

lemma bivariate_trailing_factorization {ι : Type}
    (p : MvPolynomial (Fin 2) ℂ) (c : PuiseuxAmbient) (hc : c ≠ 0)
    (s : Finset ι) (x : ι → PuiseuxAmbient) (mu : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ (x i).orderTop)
    (hp : bivariateSeries p = Polynomial.C c *
      ∏ i ∈ s, (Polynomial.X - Polynomial.C (x i)) ^ mu i) :
    ∃ a : ℂ, a ≠ 0 ∧ bivariateOther (trailingCoefficient 0 p) =
      Polynomial.C a * ∏ i ∈ s, (Polynomial.X - Polynomial.C ((x i).coeff 0)) ^ mu i := by
  exact trailing_series_product p c hc s x mu hx hp

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

lemma polynomial_trailingCoeff_map_injective {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).trailingCoeff = f p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_zero]
  have hm : (p.map f).coeff p.natTrailingDegree ≠ 0 := by
    rw [Polynomial.coeff_map]
    exact fun h => (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp) (hf (h.trans f.map_zero.symm))
  have hp' : p.map f ≠ 0 := fun h => hm (by simp [h])
  have hd : (p.map f).natTrailingDegree = p.natTrailingDegree :=
    le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hm)
      (Polynomial.le_natTrailingDegree hp' (fun j hj => by
        rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj, map_zero]))
  rw [Polynomial.trailingCoeff, hd, Polynomial.coeff_map]
  rfl

end APSCounting893.Main
end Component_13

section Component_14

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma bivariateSeries_injective {K : Type} [CommRing K] :
    Function.Injective (bivariateSeries (K := K)) := by
  intro p q hpq
  apply splitBivariate_injective
  apply (Polynomial.algebraMap_hahnSeries_injective (Γ := ℚ) (R := Polynomial K))
  rw [← polynomialToHahn_bivariateSeries, ← polynomialToHahn_bivariateSeries, hpq]

noncomputable def threeVariableSeries {K : Type} [CommRing K] :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) (HahnSeries ℚ K) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp HahnSeries.C)
    (fun j => if j = 0 then MvPolynomial.X 0 else
      if j = 1 then MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : K)) else MvPolynomial.X 1)

lemma split_threeVariableSeries {K : Type} [CommRing K] (p : MvPolynomial (Fin 3) K) :
    splitBivariate (threeVariableSeries p) =
      Polynomial.map bivariateSeries (MvPolynomial.finSuccEquiv K 2 p) := by
  have hh : (splitBivariate (K := HahnSeries ℚ K)).comp threeVariableSeries =
      (Polynomial.mapRingHom (bivariateSeries (K := K))).comp (MvPolynomial.finSuccEquiv K 2).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change splitBivariate (threeVariableSeries (MvPolynomial.C c)) =
        Polynomial.map bivariateSeries (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C c))
      have hc : MvPolynomial.finSuccEquiv K 2 (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := (MvPolynomial.finSuccEquiv K 2).commutes c
      rw [hc]
      simp [threeVariableSeries, splitBivariate, bivariateSeries]
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [threeVariableSeries, splitBivariate, bivariateSeries, MvPolynomial.finSuccEquiv_X_zero]
      · change splitBivariate (threeVariableSeries (MvPolynomial.X i.succ)) =
          Polynomial.map bivariateSeries (MvPolynomial.finSuccEquiv K 2 (MvPolynomial.X i.succ))
        rw [MvPolynomial.finSuccEquiv_X_succ]
        fin_cases i <;> simp [threeVariableSeries, splitBivariate, bivariateSeries]
  exact RingHom.congr_fun hh p

lemma threeVariableSeries_trailing {K : Type} [CommRing K] (p : MvPolynomial (Fin 3) K) :
    bivariateOther (trailingCoefficient 0 (threeVariableSeries p)) =
      bivariateSeries (MvPolynomial.finSuccEquiv K 2 p).trailingCoeff := by
  rw [← bivariate_trailingCoeff, split_threeVariableSeries,
    polynomial_trailingCoeff_map_injective _ bivariateSeries_injective]

end APSCounting893.Main
end Component_14

section Component_15

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma splitVariable_X {K : Type} [CommRing K] {n : ℕ} (v j : Fin n) :
    splitVariable v (MvPolynomial.X j : MvPolynomial (Fin n) K) =
      if j = v then Polynomial.X else Polynomial.C (MvPolynomial.X j) := by
  classical
  change splitVariable v (monomial (Finsupp.single j 1) (1 : K)) = _
  rw [splitVariable_monomial]
  by_cases hj : j = v
  · subst j
    simp
    exact Polynomial.monomial_one_one_eq_X
  · simp [hj, Ne.symm hj, Finsupp.single_apply]
    rfl

noncomputable def splitVariableRingHom {K : Type} [CommRing K] {n : ℕ} (v : Fin n) :
    MvPolynomial (Fin n) K →+* Polynomial (MvPolynomial (Fin n) K) where
  toFun := splitVariable v
  map_zero' := splitVariable_zero v
  map_one' := by simpa using splitVariable_C v (1 : K)
  map_add' := splitVariable_add v
  map_mul' := splitVariable_mul v

lemma splitVariable_fin_zero {K : Type} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin (n+1)) K) :
    splitVariable 0 p = Polynomial.map (MvPolynomial.rename Fin.succ).toRingHom
      (MvPolynomial.finSuccEquiv K n p) := by
  have hh : (splitVariableRingHom (K := K) (0 : Fin (n+1))) =
      (Polynomial.mapRingHom (MvPolynomial.rename Fin.succ).toRingHom).comp (MvPolynomial.finSuccEquiv K n).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change splitVariable 0 (MvPolynomial.C c) = _
      rw [splitVariable_C]
      have hc : MvPolynomial.finSuccEquiv K n (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := (MvPolynomial.finSuccEquiv K n).commutes c
      change Polynomial.C (MvPolynomial.C c) = Polynomial.map _ (MvPolynomial.finSuccEquiv K n (MvPolynomial.C c))
      rw [hc, Polynomial.map_C]
      change Polynomial.C (MvPolynomial.C c) = Polynomial.C (MvPolynomial.rename Fin.succ (MvPolynomial.C c))
      rw [MvPolynomial.rename_C]
    · intro j
      change splitVariable 0 (MvPolynomial.X j) = _
      rw [splitVariable_X]
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [MvPolynomial.finSuccEquiv_X_zero]
      · simp [MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun hh p

lemma trailingCoefficient_fin_zero {K : Type} [CommRing K] {n : ℕ}
    (p : MvPolynomial (Fin (n+1)) K) :
    trailingCoefficient 0 p = MvPolynomial.rename Fin.succ (MvPolynomial.finSuccEquiv K n p).trailingCoeff := by
  rw [trailingCoefficient_eq_split, splitVariable_fin_zero,
    polynomial_trailingCoeff_map_injective _ (MvPolynomial.rename_injective _ (Fin.succ_injective n))]
  rfl

end APSCounting893.Main
end Component_15

section Component_16

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma splitVariable_rename_succ {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    splitVariable v.succ (MvPolynomial.rename Fin.succ p) =
      Polynomial.map (MvPolynomial.rename Fin.succ).toRingHom (splitVariable v p) := by
  have hh : (splitVariableRingHom (K := K) v.succ).comp (MvPolynomial.rename Fin.succ).toRingHom =
      (Polynomial.mapRingHom (MvPolynomial.rename Fin.succ).toRingHom).comp (splitVariableRingHom v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change splitVariable v.succ (MvPolynomial.rename Fin.succ (MvPolynomial.C c)) = _
      rw [MvPolynomial.rename_C, splitVariable_C]
      change Polynomial.C (MvPolynomial.C c) = Polynomial.map _ (splitVariable v (MvPolynomial.C c))
      rw [splitVariable_C, Polynomial.map_C]
      change Polynomial.C (MvPolynomial.C c) = Polynomial.C (MvPolynomial.rename Fin.succ (MvPolynomial.C c))
      rw [MvPolynomial.rename_C]
    · intro j
      change splitVariable v.succ (MvPolynomial.rename Fin.succ (MvPolynomial.X j)) = _
      rw [MvPolynomial.rename_X, splitVariable_X]
      change (if j.succ = v.succ then Polynomial.X else Polynomial.C (MvPolynomial.X j.succ)) =
        Polynomial.map _ (splitVariable v (MvPolynomial.X j))
      rw [splitVariable_X]
      simp only [Fin.succ_inj]
      by_cases hj : j = v
      · simp [hj]
      · simp [hj]
  exact RingHom.congr_fun hh p

lemma trailingCoefficient_rename_succ {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) :
    trailingCoefficient v.succ (MvPolynomial.rename Fin.succ p) =
      MvPolynomial.rename Fin.succ (trailingCoefficient v p) := by
  rw [trailingCoefficient_eq_split, splitVariable_rename_succ,
    polynomial_trailingCoeff_map_injective _ (MvPolynomial.rename_injective _ (Fin.succ_injective n)),
    ← trailingCoefficient_eq_split]
  rfl

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonFormal (R : Aux) : MvPolynomial (Fin 3) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 3 R).trailingCoeff

noncomputable def wFormal (R : Aux) : MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.finSuccEquiv ℂ 2 (epsilonFormal R)).trailingCoeff

lemma trailingEpsilonResultant_eq (R : Aux) :
    trailingEpsilonResultant R = threeVariableSeries (epsilonFormal R) := by
  unfold trailingEpsilonResultant
  rw [trailingCoefficient_fin_zero]
  change MvPolynomial.eval₂ (MvPolynomial.C.comp HahnSeries.C)
      (fun v : Fin 4 => if v = 1 then MvPolynomial.X 0 else if v = 3 then MvPolynomial.X 1
        else if v = 2 then MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)
      (MvPolynomial.rename Fin.succ (epsilonFormal R)) = _
  rw [MvPolynomial.eval₂_rename]
  change MvPolynomial.eval₂ _ _ (epsilonFormal R) = MvPolynomial.eval₂ _ _ (epsilonFormal R)
  apply MvPolynomial.eval₂_congr
  intro v e he hp
  fin_cases v <;> simp [Function.comp_def]

set_option maxRecDepth 4096 in
lemma wFormal_series_eq (R : Aux) :
    bivariateSeries (wFormal R) = bivariateOther (trailingCoefficient 0 (trailingEpsilonResultant R)) := by
  rw [trailingEpsilonResultant_eq, threeVariableSeries_trailing]
  rfl

lemma resultantCriterion_eq_formal (R : Aux) :
    resultantCriterion R = bivariateOther (trailingCoefficient 0 (wFormal R)) := by
  have h1 : trailingCoefficient (1 : Fin 4) (trailingCoefficient 0 R) =
      MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (wFormal R)) := by
    calc
      trailingCoefficient (1 : Fin 4) (trailingCoefficient 0 R) =
          trailingCoefficient (0 : Fin 3).succ (MvPolynomial.rename Fin.succ (epsilonFormal R)) := by
        rw [trailingCoefficient_fin_zero]
        rfl
      _ = MvPolynomial.rename Fin.succ (trailingCoefficient 0 (epsilonFormal R)) :=
        trailingCoefficient_rename_succ (0 : Fin 3) (epsilonFormal R)
      _ = MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (wFormal R)) := by
        exact congrArg (MvPolynomial.rename Fin.succ) (trailingCoefficient_fin_zero (epsilonFormal R))
  have h2 : trailingCoefficient (2 : Fin 4) (trailingCoefficient 1 (trailingCoefficient 0 R)) =
      MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (trailingCoefficient 0 (wFormal R))) := by
    rw [h1]
    calc
      trailingCoefficient (2 : Fin 4) (MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (wFormal R))) =
          MvPolynomial.rename Fin.succ (trailingCoefficient (1 : Fin 3) (MvPolynomial.rename Fin.succ (wFormal R))) :=
        trailingCoefficient_rename_succ (1 : Fin 3) (MvPolynomial.rename Fin.succ (wFormal R))
      _ = _ := congrArg (MvPolynomial.rename Fin.succ)
        (trailingCoefficient_rename_succ (0 : Fin 2) (wFormal R))

  unfold resultantCriterion nestedTrailing
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h2]
  change MvPolynomial.eval₂ Polynomial.C (fun i : Fin 4 => if i = 3 then Polynomial.X else 0)
    (MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (trailingCoefficient 0 (wFormal R)))) = _
  rw [MvPolynomial.eval₂_rename, MvPolynomial.eval₂_rename]
  change MvPolynomial.eval₂ _ _ (trailingCoefficient 0 (wFormal R)) =
    MvPolynomial.eval₂ _ _ (trailingCoefficient 0 (wFormal R))
  apply MvPolynomial.eval₂_congr
  intro i e he hp
  fin_cases i <;> simp [Function.comp_def]

end APSCounting893.Main
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_HAtPoint_zero (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) :
    coefficientIn (0 : Fin 2) 0 (HAtPoint F lambda z) =
      X 1 * C (z 0 ^ 2) - C (z 0 * ∑ j : Fin (F.n + 1),
        HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by
  classical
  simp [HAtPoint, coefficientIn_add, coefficientIn_sub, coefficientIn_sum,
    coefficientIn_zero_mul, coefficientIn_zero_C, coefficientIn_zero_X, coefficientIn_zero_pow]

lemma trailing_HAtPoint_affine (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z 0 ≠ 0) :
    trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) =
      X 1 * C (z 0 ^ 2) - C (z 0 * ∑ j : Fin (F.n + 1),
        HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by
  have hnonzero : coefficientIn (0 : Fin 2) 0 (HAtPoint F lambda z) ≠ 0 := by
    rw [coefficientIn_HAtPoint_zero]
    intro h
    have hc := congrArg (MvPolynomial.coeff (Finsupp.single (1 : Fin 2) 1)) h
    rw [mul_comm (X 1) (C (z 0 ^ 2)), coeff_sub, coeff_C_mul] at hc
    have hm : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 :=
      Ne.symm (Finsupp.single_ne_zero.mpr Nat.one_ne_zero)
    simp only [coeff_X_same, mul_one, coeff_C, if_neg hm, sub_zero, coeff_zero] at hc
    exact pow_ne_zero 2 hz hc
  rw [trailingCoefficient_eq_of_zero_coeff _ _ hnonzero, coefficientIn_HAtPoint_zero]

lemma trailing_HAtPoint_chart_one (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z 0 = 1) :
    trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) =
      X 1 - C (∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by
  rw [trailing_HAtPoint_affine F lambda z (by rw [hz]; exact one_ne_zero), hz]
  simp

lemma trailingCoefficient_self_X {K : Type} [CommRing K] [Nontrivial K] {n : ℕ}
    (v : Fin n) : trailingCoefficient v (X v : MvPolynomial (Fin n) K) = 1 := by
  classical
  have hcoef : coefficientIn v 1 (X v : MvPolynomial (Fin n) K) = 1 := by
    change coefficientIn v 1 (monomial (Finsupp.single v 1) 1) = _
    rw [coefficientIn_monomial]
    simp
  have he := trailingCoefficient_eq_of_min v (X v : MvPolynomial (Fin n) K) 1
    (by rw [hcoef]; exact one_ne_zero) (fun j hj => by
      have hj0 : j = 0 := by omega
      subst j
      simp [coefficientIn_zero_X])
  exact he.trans hcoef

end APSCounting893.Main
end Component_18

section Component_19

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma coefficientIn_zero_diagonal {K : Type} [CommRing K] {n N : ℕ}
    (v : Fin n) (z : Fin N → K) :
    coefficientIn v 0 (∑ j : Fin N, X v ^ (j.val + 1) * C (z j ^ 2)) = 0 := by
  classical
  simp [coefficientIn_sum, coefficientIn_zero_mul, coefficientIn_zero_pow,
    coefficientIn_zero_X, coefficientIn_zero_C]

lemma diagonal_form_cons {K : Type} [CommRing K] {n N : ℕ}
    (v : Fin n) (z : Fin (N + 1) → K) :
    (∑ j : Fin (N + 1), X v ^ (j.val + 1) * C (z j ^ 2)) =
      X v * (C (z 0 ^ 2) + ∑ j : Fin N, X v ^ (j.val + 1) * C (z j.succ ^ 2)) := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, zero_add, pow_one, Fin.val_succ]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ]
  ring

lemma trailing_diagonal_constant {K : Type} [Field K] {n N : ℕ}
    (v : Fin n) (z : Fin N → K) (hz : z ≠ 0) :
    ∃ c : K, c ≠ 0 ∧
      trailingCoefficient v (∑ j : Fin N, X v ^ (j.val + 1) * C (z j ^ 2)) = C c := by
  classical
  induction N with
  | zero =>
    exact False.elim (hz (funext (fun j => Fin.elim0 j)))
  | succ N ih =>
    rw [diagonal_form_cons, trailingCoefficient_mul, trailingCoefficient_self_X, one_mul]
    by_cases hhead : z 0 = 0
    · have htail : (fun j : Fin N => z j.succ) ≠ 0 := by
        intro h
        apply hz
        funext j
        exact Fin.cases hhead (fun k => congrFun h k) j
      obtain ⟨c, hc, hct⟩ := ih (fun j => z j.succ) htail
      refine ⟨c, hc, ?_⟩
      simpa only [hhead, zero_pow (by decide : 2 ≠ 0), map_zero, zero_add] using hct
    · have hc : z 0 ^ 2 ≠ 0 := pow_ne_zero 2 hhead
      refine ⟨z 0 ^ 2, hc, ?_⟩
      have hcoef : coefficientIn v 0
          (C (z 0 ^ 2) + ∑ j : Fin N, X v ^ (j.val + 1) * C (z j.succ ^ 2)) = C (z 0 ^ 2) := by
        rw [coefficientIn_add, coefficientIn_zero_C, coefficientIn_zero_diagonal, add_zero]
      have hcoeff : coefficientIn v 0
          (C (z 0 ^ 2) + ∑ j : Fin N, X v ^ (j.val + 1) * C (z j.succ ^ 2)) ≠ 0 := by
        rw [hcoef]
        intro hzC
        have hh := congrArg (MvPolynomial.coeff (0 : Fin n →₀ ℕ)) hzC
        apply hc
        simpa only [coeff_C, if_pos rfl, ite_true, coeff_zero] using hh
      rw [trailingCoefficient_eq_of_zero_coeff _ _ hcoeff, hcoef]

lemma trailing_HAtPoint_infinity (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z ≠ 0) (h0 : z 0 = 0) :
    ∃ c : PuiseuxAmbient, c ≠ 0 ∧ trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) = C c := by
  have htail : (fun j : Fin (F.n + (F.n + 1)) => z j.succ) ≠ 0 := by
    intro h
    apply hz
    funext j
    exact Fin.cases h0 (fun k => congrFun h k) j
  obtain ⟨c, hc, hct⟩ := trailing_diagonal_constant (0 : Fin 2) (fun j => z j.succ) htail
  refine ⟨c, hc, ?_⟩
  simpa only [HAtPoint, h0, zero_pow (by decide : 2 ≠ 0), map_zero, mul_zero, zero_mul,
    sub_zero, sub_self, zero_add] using hct

end APSCounting893.Main
end Component_19

section Component_20

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma trailing_HAtPoint_affine_scaled (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) (hz : z 0 ≠ 0) :
    trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) = C (z 0 ^ 2) *
      (X 1 - C ((∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) / z 0)) := by
  rw [trailing_HAtPoint_affine F lambda z hz]
  have he : z 0 * (∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) =
      z 0 ^ 2 * ((∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) / z 0) := by
    field_simp [hz]
  rw [he, map_mul]
  ring

open Classical in
lemma trailing_separating_product (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (S : Finset (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient))
    (hS : ∀ z ∈ S, z ≠ 0)
    (mu : (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) → ℕ) :
    ∃ c : PuiseuxAmbient, c ≠ 0 ∧
      trailingCoefficient (0 : Fin 2) (∏ z ∈ S, HAtPoint F lambda z ^ mu z) = C c *
        ∏ z ∈ S.filter (fun z => z 0 ≠ 0),
          (X 1 - C ((∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) / z 0)) ^ mu z := by
  classical
  let lin := fun z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient =>
    (X 1 - C ((∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) / z 0) :
      MvPolynomial (Fin 2) PuiseuxAmbient)
  have heach : ∀ z, ∃ c : PuiseuxAmbient, z ∈ S → c ≠ 0 ∧
      trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) =
        C c * (if z 0 ≠ 0 then lin z else 1) := by
    intro z
    by_cases hzS : z ∈ S
    · by_cases h0 : z 0 = 0
      · obtain ⟨c, hc, hct⟩ := trailing_HAtPoint_infinity F lambda z (hS z hzS) h0
        exact ⟨c, fun _ => ⟨hc, by simpa only [h0, ne_eq, not_true_eq_false, ite_false, mul_one] using hct⟩⟩
      · exact ⟨z 0 ^ 2, fun _ => ⟨pow_ne_zero 2 h0, by
          rw [if_pos h0]
          exact trailing_HAtPoint_affine_scaled F lambda z h0⟩⟩
    · exact ⟨1, fun hz => False.elim (hzS hz)⟩
  choose scalar hscalar using heach
  refine ⟨∏ z ∈ S, scalar z ^ mu z, Finset.prod_ne_zero_iff.mpr (fun z hz => pow_ne_zero _ (hscalar z hz).1), ?_⟩
  rw [trailingCoefficient_prod]
  simp only [trailingCoefficient_pow]
  calc
    ∏ z ∈ S, trailingCoefficient (0 : Fin 2) (HAtPoint F lambda z) ^ mu z =
        ∏ z ∈ S, (C (scalar z) * (if z 0 ≠ 0 then lin z else 1)) ^ mu z := by
      apply Finset.prod_congr rfl
      intro z hz
      rw [(hscalar z hz).2]
    _ = C (∏ z ∈ S, scalar z ^ mu z) *
        ∏ z ∈ S.filter (fun z => z 0 ≠ 0), lin z ^ mu z := by
      simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib]
      rw [← map_prod]
      congr 1
      simp only [ite_pow, one_pow, Finset.prod_filter]

end APSCounting893.Main
end Component_20

section Component_21

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def tCoefficientHom : Polynomial ℂ →+* PuiseuxAmbient :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ))

noncomputable def tAuxHom : Aux →+* PuiseuxAmbient :=
  MvPolynomial.eval₂Hom HahnSeries.C
    (fun v : Fin 4 => if v = 2 then HahnSeries.single (1 : ℚ) (1 : ℂ) else 0)

lemma tCoefficient_C (c : ℂ) : tCoefficientHom (Polynomial.C c) = HahnSeries.C c := by
  simp [tCoefficientHom]

lemma tAux_polynomial_coefficients (p : Polynomial ℂ) :
    tAuxHom ((Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) p) =
      tCoefficientHom p := by
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [tAuxHom, tCoefficientHom]
    · simp [tAuxHom, tCoefficientHom]
  exact RingHom.congr_fun heq p

lemma equationWithAux_specializes (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) (x : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    MvPolynomial.eval₂ tAuxHom x (equationWithAux F c alpha i) =
      MvPolynomial.eval₂ tCoefficientHom x
        (affineLineEquations F c alpha (Fin.cast (Nat.add_comm _ _) i)) := by
  rw [equationWithAux, MvPolynomial.eval₂_map]
  have heq : tAuxHom.comp (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (2 : Fin 4))) =
      tCoefficientHom := by
    exact RingHom.ext tAux_polynomial_coefficients
  rw [heq]

lemma affineLineEquations_iff (F : ReducedMap) (D : LineData F)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) :
    (∀ i, MvPolynomial.eval₂ tCoefficientHom z (affineLineEquations F D.c D.alpha i) = 0) ↔
      (∀ j : Fin (F.n + 1), z (j.natAdd F.n) =
        MvPolynomial.eval₂ HahnSeries.C (fun i => z (i.castAdd (F.n + 1))) (F.F j)) ∧
      (∀ j : Fin F.n, z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ)) := by
  have hcomp : tCoefficientHom.comp Polynomial.C = HahnSeries.C := by
    exact RingHom.ext tCoefficient_C
  have hout (j : Fin (F.n + 1)) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.castAdd F.n)) =
      z (j.natAdd F.n) - MvPolynomial.eval₂ HahnSeries.C
        (fun i => z (i.castAdd (F.n + 1))) (F.F j) := by
    simp only [affineLineEquations, Fin.addCases_left, MvPolynomial.eval₂_sub,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename, MvPolynomial.eval₂_map, hcomp]
    rfl
  have hline (j : Fin F.n) :
      MvPolynomial.eval₂ tCoefficientHom z
        (affineLineEquations F D.c D.alpha (j.natAdd (F.n + 1))) =
      z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) -
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ) := by
    simp [affineLineEquations, tCoefficientHom]
  constructor
  · intro h
    exact ⟨fun j => sub_eq_zero.mp ((hout j).symm.trans (h _)),
      fun j => sub_eq_zero.mp ((hline j).symm.trans (h _))⟩
  · rintro ⟨ho, hl⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [hout, ho, sub_self]
    · rw [hline, hl, sub_self]

end APSCounting893.Main
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_23

section Component_24

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonRegular : nonnegativeHahnRing PuiseuxAmbient :=
  Classical.choose (hahnResidue_single_one (K := PuiseuxAmbient))

lemma epsilonRegular_val : epsilonRegular.val = HahnSeries.single (1 : ℚ) (1 : PuiseuxAmbient) :=
  (Classical.choose_spec (hahnResidue_single_one (K := PuiseuxAmbient))).1

lemma epsilonRegular_residue : hahnResidueHom PuiseuxAmbient epsilonRegular = 0 :=
  (Classical.choose_spec (hahnResidue_single_one (K := PuiseuxAmbient))).2

noncomputable def epsilonAuxHom : Aux →+* EpsilonAmbient :=
  MvPolynomial.eval₂Hom (HahnSeries.C.comp HahnSeries.C)
    (fun v : Fin 4 => if v = 0 then HahnSeries.single (1 : ℚ) 1
      else if v = 2 then HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)

noncomputable def epsilonAuxLift : Aux →+* nonnegativeHahnRing PuiseuxAmbient :=
  MvPolynomial.eval₂Hom ((hahnConstantLift PuiseuxAmbient).comp HahnSeries.C)
    (fun v : Fin 4 => if v = 0 then epsilonRegular
      else if v = 2 then hahnConstantLift PuiseuxAmbient (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)

lemma epsilonAuxLift_underlying :
    (nonnegativeHahnRing PuiseuxAmbient).subtype.comp epsilonAuxLift = epsilonAuxHom := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [epsilonAuxLift, epsilonAuxHom, hahnConstantLift]
  · intro v
    fin_cases v <;> simp [epsilonAuxLift, epsilonAuxHom, hahnConstantLift, epsilonRegular_val]

lemma epsilonAuxLift_residue :
    (hahnResidueHom PuiseuxAmbient).comp epsilonAuxLift = tAuxHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [epsilonAuxLift, tAuxHom, hahnResidue_constant]
  · intro v
    fin_cases v <;> simp [epsilonAuxLift, tAuxHom, hahnResidue_constant, epsilonRegular_residue]

lemma epsilon_specialization_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ)
    (q : Fin (F.n + (F.n + 1) + 1) → EpsilonAmbient)
    (hq : ∀ j, 0 ≤ (q j).orderTop)
    (hroot : ∀ i, MvPolynomial.eval₂ epsilonAuxHom q (perturbedEquation F c alpha degrees i) = 0) :
    ∀ i, MvPolynomial.eval₂ tAuxHom (fun j => (q j).coeff 0) (homogenizedEquation F c alpha degrees i) = 0 := by
  let qlift : Fin (F.n + (F.n + 1) + 1) → nonnegativeHahnRing PuiseuxAmbient := fun j => ⟨q j, hq j⟩
  intro i
  have hlift : MvPolynomial.eval₂ epsilonAuxLift qlift (perturbedEquation F c alpha degrees i) = 0 := by
    apply Subtype.val_injective
    change (nonnegativeHahnRing PuiseuxAmbient).subtype
      (MvPolynomial.eval₂ epsilonAuxLift qlift (perturbedEquation F c alpha degrees i)) = 0
    rw [MvPolynomial.hom_eval₂, epsilonAuxLift_underlying]
    exact hroot i
  have h := congrArg (hahnResidueHom PuiseuxAmbient) hlift
  rw [MvPolynomial.hom_eval₂, map_zero, epsilonAuxLift_residue] at h
  change MvPolynomial.eval₂ tAuxHom (fun j => (q j).coeff 0) (perturbedEquation F c alpha degrees i) = 0 at h
  simpa [perturbedEquation, tAuxHom] using h

lemma epsilon_limit_homogeneous (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F c alpha degrees)
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F c alpha degrees) :
    z ≠ 0 ∧ ∀ i, MvPolynomial.eval₂ tAuxHom z (homogenizedEquation F c alpha degrees i) = 0 := by
  obtain ⟨q, hq, hmin, hroot, hz⟩ := hz
  have hq0 : (fun j => (q j).coeff 0) ≠ 0 := by
    obtain ⟨j, hj⟩ := hmin
    intro h
    have hh := congrFun h j
    exact HahnSeries.coeff_orderTop_ne hj hh
  have heq := epsilon_specialization_homogeneous F c alpha degrees q (fun j => (hq j).2) hroot
  rw [hz]
  refine ⟨projectiveRepresentative_ne_zero _ hq0, ?_⟩
  intro i
  apply homogeneous_root_projectiveRepresentative (homogenizedEquation F c alpha degrees i) (degrees i)
    (homogenizeAll_homogeneous _ _ (hdegrees i).2.2) tAuxHom _ hq0 (heq i)

end APSCounting893.Main
end Component_24

section Component_25

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def epsilonAffineOutput (F : RawMap)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient) : Affine PuiseuxAmbient (F.n+1) :=
  fun j => z (j.natAdd F.n).succ / z 0

lemma epsilon_affine_output_integral (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F D.c D.alpha degrees) (hz0 : z 0 ≠ 0) :
    (∀ j, PuiseuxIntegral (epsilonAffineOutput F z j)) ∧
      (fun j => residue (epsilonAffineOutput F z j)) ∈ zeroFiber F D.c :=
  (affine_perturbation_residue_coverage F D degrees hdegrees).1 z hz hz0

lemma epsilon_affine_output_residues_cover (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    {y : Affine ℂ (F.n+1) | ∃ z ∈ epsilonLimitSet F D.c D.alpha degrees,
      z 0 ≠ 0 ∧ (fun j => residue (epsilonAffineOutput F z j)) = y} = zeroFiber F D.c := by
  ext y
  constructor
  · rintro ⟨z, hz, hz0, rfl⟩
    exact (epsilon_affine_output_integral F D degrees hdegrees z hz hz0).2
  · intro hy
    exact (affine_perturbation_residue_coverage F D degrees hdegrees).2 y hy

lemma epsilonAffineOutput_rescale (F : RawMap)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient) (a : PuiseuxAmbient) (ha : a ≠ 0) :
    epsilonAffineOutput F (a • z) = epsilonAffineOutput F z := by
  funext j
  simp only [epsilonAffineOutput, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ ha

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open HahnSeries
namespace APSCounting893.Main

noncomputable def seriesSeparatingForm {n : ℕ} (lambda : Affine ℂ n)
    (y : Affine PuiseuxAmbient n) : PuiseuxAmbient := ∑ j, HahnSeries.C (lambda j) * y j

lemma seriesSeparatingForm_regular_residue {n : ℕ} (lambda : Affine ℂ n)
    (y : Affine PuiseuxAmbient n) (hy : ∀ j, 0 ≤ (y j).orderTop) :
    0 ≤ (seriesSeparatingForm lambda y).orderTop ∧
      residue (seriesSeparatingForm lambda y) = separatingForm lambda (fun j => residue (y j)) := by
  let yl : Fin n → nonnegativeHahnRing ℂ := fun j => ⟨y j, hy j⟩
  let s : nonnegativeHahnRing ℂ := ∑ j, hahnConstantLift ℂ (lambda j) * yl j
  have hval : s.val = seriesSeparatingForm lambda y := by
    change (nonnegativeHahnRing ℂ).subtype s = _
    rw [map_sum]
    unfold seriesSeparatingForm
    apply Finset.sum_congr rfl
    intro j hj
    rw [map_mul]
    rfl
  constructor
  · rw [← hval]
    exact s.property
  · rw [← hval]
    change hahnResidueHom ℂ s = ∑ j, lambda j * (y j).coeff 0
    dsimp only [s]
    simp only [map_sum, map_mul, hahnResidue_constant]
    rfl

lemma epsilon_series_separating_integral (F : ReducedMap) (D : LineData F)
    (lambda : Affine ℂ (F.n+1))
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (z : Fin (F.n + (F.n+1)+1) → PuiseuxAmbient)
    (hz : z ∈ epsilonLimitSet F D.c D.alpha degrees) (hz0 : z 0 ≠ 0) :
    0 ≤ (seriesSeparatingForm lambda (epsilonAffineOutput F z)).orderTop ∧
      residue (seriesSeparatingForm lambda (epsilonAffineOutput F z)) =
        separatingForm lambda (fun j => residue (epsilonAffineOutput F z j)) :=
  seriesSeparatingForm_regular_residue lambda _ (fun j =>
    ((epsilon_affine_output_integral F D degrees hdegrees z hz hz0).1 j).2)

end APSCounting893.Main
end Component_26

section Component_27

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma HAtPoint_rescale (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (z : Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) (a : PuiseuxAmbient) :
    HAtPoint F lambda (a • z) = MvPolynomial.C (a^2) * HAtPoint F lambda z := by
  have hsum : (∑ j : Fin (F.n+1), HahnSeries.C (lambda j) * (a*z (j.natAdd F.n).succ)) =
      a * ∑ j : Fin (F.n+1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hdiag : (∑ j : Fin (F.n+(F.n+1)),
      MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C ((a*z j.succ)^2)) =
      MvPolynomial.C (a^2) * ∑ j : Fin (F.n+(F.n+1)),
        MvPolynomial.X (0 : Fin 2) ^ (j.val+1) * MvPolynomial.C (z j.succ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow, map_mul]
    ring
  simp only [HAtPoint, Pi.smul_apply, smul_eq_mul]
  rw [hsum, hdiag]
  rw [mul_pow, map_mul]
  have hterm : (a*z 0) * (a * ∑ j, HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) =
      a^2 * (z 0 * ∑ j, HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) := by ring
  rw [hterm, map_mul]
  ring

lemma HAtPoint_projective_product (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (mu : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ)
    (reps : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hreps : ∀ z ∈ S, ∃ a : PuiseuxAmbient, a ≠ 0 ∧ reps z = a • z) :
    ∃ c : PuiseuxAmbient, c ≠ 0 ∧
      (∏ z ∈ S, HAtPoint F lambda (reps z) ^ mu z) =
        MvPolynomial.C c * ∏ z ∈ S, HAtPoint F lambda z ^ mu z := by
  classical
  have hex : ∀ z, ∃ a : PuiseuxAmbient, a ≠ 0 ∧ (z ∈ S → reps z = a • z) := by
    intro z
    by_cases hz : z ∈ S
    · obtain ⟨a, ha, he⟩ := hreps z hz
      exact ⟨a, ha, fun _ => he⟩
    · exact ⟨1, one_ne_zero, fun h => False.elim (hz h)⟩
  choose a ha using hex
  refine ⟨∏ z ∈ S, (a z ^ 2) ^ mu z,
    Finset.prod_ne_zero_iff.mpr (fun z hz => pow_ne_zero _ (pow_ne_zero _ (ha z).1)), ?_⟩
  calc
    ∏ z ∈ S, HAtPoint F lambda (reps z) ^ mu z =
        ∏ z ∈ S, (MvPolynomial.C (a z ^ 2) * HAtPoint F lambda z) ^ mu z := by
      apply Finset.prod_congr rfl
      intro z hz
      rw [(ha z).2 hz, HAtPoint_rescale]
    _ = _ := by
      simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]

lemma separatingSeries_chart (F : RawMap) (lambda : Affine ℂ (F.n+1))
    (z : Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) :
    (∑ j : Fin (F.n+1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) / z 0 =
      seriesSeparatingForm lambda (epsilonAffineOutput F z) := by
  unfold seriesSeparatingForm epsilonAffineOutput
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_div_assoc _ _ _

end APSCounting893.Main
end Component_27

section Component_28

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace APSCounting893.Main

open Classical in
lemma positive_product_regroup {α β R : Type} [CommMonoid R]
    (s : Finset α) (r : α → β) (mu : α → ℕ) (hmu : ∀ z ∈ s, 0 < mu z) (f : β → R) :
    ∃ M : β → ℕ, (∀ y ∈ s.image r, 0 < M y) ∧
      (∏ z ∈ s, f (r z) ^ mu z) = ∏ y ∈ s.image r, f y ^ M y := by
  classical
  let M : β → ℕ := fun y => ∑ z ∈ s.filter (fun z => r z = y), mu z
  refine ⟨M, ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact lt_of_lt_of_le (hmu z hz) (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨hz, rfl⟩))
  · symm
    calc
      ∏ y ∈ s.image r, f y ^ M y =
          ∏ y ∈ s.image r, ∏ z ∈ s.filter (fun z => r z = y), f (r z) ^ mu z := by
        apply Finset.prod_congr rfl
        intro y hy
        rw [show M y = ∑ z ∈ s.filter (fun z => r z = y), mu z from rfl,
          ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl
        intro z hz
        rw [(Finset.mem_filter.mp hz).2]
      _ = ∏ z ∈ s, f (r z) ^ mu z :=
        Finset.prod_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem r hz) _

end APSCounting893.Main
end Component_28

section Component_29

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

lemma separatingForm_zero {n : ℕ} (lambda : Affine ℂ n) : separatingForm lambda 0 = 0 := by
  simp [separatingForm]

lemma normalization_zero {n : ℕ} (c : Affine ℂ n) : normalization c 0 = 0 := by
  funext i
  simp [normalization, normalizationPolynomials, evaluate]

lemma aps_iff_separating_product_zero (F : ReducedMap) (D : LineData F)
    (lambda : Affine ℂ (F.n + 1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (S : Finset (Affine ℂ (F.n + 1))) (hS : (S : Set _) = zeroFiber F D.c)
    (c : ℂ) (hc : c ≠ 0) (M : Affine ℂ (F.n + 1) → ℕ)
    (hM : ∀ y ∈ S, 0 < M y) :
    hasAPS F.F ↔ (Polynomial.C c * ∏ y ∈ S,
      (Polynomial.X - Polynomial.C (separatingForm lambda y)) ^ M y).eval 0 = 0 := by
  classical
  have hzero : (0 : Affine ℂ (F.n + 1)) ∈ zeroFiber F D.c ↔ hasAPS F.F := by
    simp only [zeroFiber, Set.mem_setOf_eq, hasAPS, normalization_zero, and_true]
  have hEval : (Polynomial.C c * ∏ y ∈ S,
      (Polynomial.X - Polynomial.C (separatingForm lambda y)) ^ M y).eval 0 =
      c * ∏ y ∈ S, (-separatingForm lambda y) ^ M y := by
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    congr 1
    exact map_prod (Polynomial.evalRingHom 0) _ S |>.trans (by simp)
  rw [hEval]
  constructor
  · intro h
    have h0S : (0 : Affine ℂ (F.n + 1)) ∈ S := by
      change (0 : Affine ℂ (F.n + 1)) ∈ (S : Set _)
      rw [hS]
      exact hzero.mpr h
    have hz := (Finset.prod_eq_zero_iff).mpr
      (show ∃ y ∈ S, (-separatingForm lambda y) ^ M y = 0 from
        ⟨0, h0S, by rw [separatingForm_zero, neg_zero, zero_pow (hM 0 h0S).ne']⟩)
    rw [hz, mul_zero]
  · intro h
    have hp : (∏ y ∈ S, (-separatingForm lambda y) ^ M y) = 0 := (mul_eq_zero.mp h).resolve_left hc
    obtain ⟨y, hy, hpow⟩ := Finset.prod_eq_zero_iff.mp hp
    have hyzero : separatingForm lambda y = 0 := by
      by_contra hn
      exact pow_ne_zero (M y) (neg_ne_zero.mpr hn) hpow
    have hyfiber : y ∈ zeroFiber F D.c := by
      rw [← hS]
      exact hy
    have hyeq : y = 0 := hsep (Set.mem_union_left _ hyfiber) (Set.mem_union_right _ (Set.mem_singleton 0))
      (hyzero.trans (separatingForm_zero lambda).symm)
    apply hzero.mp
    rwa [← hyeq]

end APSCounting893.Main
end Component_29

section Component_30

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial HahnSeries
namespace APSCounting893.Main

lemma bivariateOther_C {K : Type} [CommRing K] (c : K) :
    bivariateOther (MvPolynomial.C c : MvPolynomial (Fin 2) K) = Polynomial.C c := by
  simp [bivariateOther]

lemma bivariateOther_X_one {K : Type} [CommRing K] :
    bivariateOther (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) = Polynomial.X := by
  simp [bivariateOther]

lemma resultant_product_specialization (F : ReducedMap) (D : LineData F)
    (lambda : Affine ℂ (F.n+1))
    (degrees : Fin (F.n+(F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees)
    (R : Aux) (S : Finset (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hS : (S : Set _) = epsilonLimitSet F D.c D.alpha degrees)
    (mu : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → ℕ)
    (hmu : ∀ z ∈ S, 0 < mu z)
    (reps : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient))
    (hreps : ∀ z ∈ S, ∃ a : PuiseuxAmbient, a ≠ 0 ∧ reps z = a • z)
    (hfactor : trailingEpsilonResultant R = ∏ z ∈ S, HAtPoint F lambda (reps z) ^ mu z) :
    ∃ (S0 : Finset (Affine ℂ (F.n+1))) (c : ℂ) (M : Affine ℂ (F.n+1) → ℕ),
      (S0 : Set _) = zeroFiber F D.c ∧ c ≠ 0 ∧ (∀ y ∈ S0, 0 < M y) ∧
      resultantCriterion R = Polynomial.C c * ∏ y ∈ S0,
        (Polynomial.X - Polynomial.C (separatingForm lambda y)) ^ M y := by
  classical
  letI : DecidableEq (Affine ℂ (F.n+1)) := Classical.decEq _
  have hmem (z) (hz : z ∈ S) : z ∈ epsilonLimitSet F D.c D.alpha degrees := by
    rw [← hS]
    exact hz
  have hnonzero : ∀ z ∈ S, z ≠ 0 := fun z hz =>
    (epsilon_limit_homogeneous F D.c D.alpha degrees hdegrees z (hmem z hz)).1
  obtain ⟨A, hA, hrep⟩ := HAtPoint_projective_product F lambda S mu reps hreps
  obtain ⟨B, hB, hwp⟩ := trailing_separating_product F lambda S hnonzero mu
  have hTC : trailingCoefficient 0 (trailingEpsilonResultant R) =
      MvPolynomial.C (A*B) * ∏ z ∈ S.filter (fun z => z 0 ≠ 0),
        (MvPolynomial.X 1 - MvPolynomial.C (seriesSeparatingForm lambda (epsilonAffineOutput F z))) ^ mu z := by
    rw [hfactor, hrep, trailingCoefficient_mul, trailingCoefficient_C, hwp]
    rw [← mul_assoc, ← map_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro z hz
    rw [separatingSeries_chart]
  let SA := S.filter (fun z => z 0 ≠ 0)
  let x := fun z => seriesSeparatingForm lambda (epsilonAffineOutput F z)
  let r : (Fin (F.n+(F.n+1)+1) → PuiseuxAmbient) → Affine ℂ (F.n+1) :=
    fun z j => residue (epsilonAffineOutput F z j)
  have hx (z) (hz : z ∈ SA) : 0 ≤ (x z).orderTop ∧
      (x z).coeff 0 = separatingForm lambda (r z) := by
    obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
    exact epsilon_series_separating_integral F D lambda degrees hdegrees z (hmem z hzS) hz0
  have hpoly : bivariateSeries (wFormal R) = Polynomial.C (A*B) *
      ∏ z ∈ SA, (Polynomial.X - Polynomial.C (x z)) ^ mu z := by
    rw [wFormal_series_eq, hTC, map_mul, bivariateOther_C, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro z hz
    rw [map_pow, map_sub, bivariateOther_X_one, bivariateOther_C]
  obtain ⟨c, hc, hct⟩ := bivariate_trailing_factorization (wFormal R) (A*B) (mul_ne_zero hA hB)
    SA x mu (fun z hz => (hx z hz).1) hpoly
  obtain ⟨M, hM, hgroup⟩ := positive_product_regroup SA r mu
    (fun z hz => hmu z (Finset.mem_filter.mp hz).1)
    (fun y => Polynomial.X - Polynomial.C (separatingForm lambda y))
  refine ⟨SA.image r, c, M, ?_, hc, hM, ?_⟩
  · rw [← epsilon_affine_output_residues_cover F D degrees hdegrees]
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hy
      obtain ⟨hzS, hz0⟩ := Finset.mem_filter.mp hz
      exact ⟨z, hmem z hzS, hz0, heq⟩
    · rintro ⟨z, hz, hz0, heq⟩
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨by change z ∈ (S : Set _); rw [hS]; exact hz, hz0⟩, heq⟩
  · rw [resultantCriterion_eq_formal, hct]
    congr 1
    calc
      ∏ z ∈ SA, (Polynomial.X - Polynomial.C ((x z).coeff 0)) ^ mu z =
          ∏ z ∈ SA, (Polynomial.X - Polynomial.C (separatingForm lambda (r z))) ^ mu z := by
        apply Finset.prod_congr rfl
        intro z hz
        rw [(hx z hz).2]
      _ = _ := hgroup

end APSCounting893.Main
end Component_30

open APSCounting893.Main

set_option autoImplicit false
set_option maxHeartbeats 4000000
open APSCounting893.Main

theorem solution (F : ReducedMap) (D : LineData F) (lambda : Affine ℂ (F.n + 1))
    (hsep : Set.InjOn (separatingForm lambda) (zeroFiber F D.c ∪ {0}))
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    ∃ (S : Finset (Affine ℂ (F.n + 1))) (c : ℂ) (M : Affine ℂ (F.n + 1) → ℕ),
      (S : Set _) = zeroFiber F D.c ∧ c ≠ 0 ∧ (∀ y ∈ S, 0 < M y) ∧
      resultantCriterion (resultantFor F D.c D.alpha lambda degrees) =
        Polynomial.C c * ∏ y ∈ S,
          (Polynomial.X - Polynomial.C (separatingForm lambda y)) ^ M y ∧
      (hasAPS F.F ↔ (resultantCriterion (resultantFor F D.c D.alpha lambda degrees)).eval 0 = 0) := by
  obtain ⟨S, hS, mu, reps, hmu, hfactor⟩ := ierardi_resultant_factorization F D lambda hsep degrees hdegrees
  obtain ⟨S0, c, M, hS0, hc, hM, heq⟩ := resultant_product_specialization F D lambda degrees hdegrees
    _ S hS mu (fun z hz => (hmu z hz).1) reps (fun z hz => (hmu z hz).2) hfactor
  refine ⟨S0, c, M, hS0, hc, hM, heq, ?_⟩
  rw [heq]
  exact aps_iff_separating_product_zero F D lambda hsep S0 hS0 c hc M hM
