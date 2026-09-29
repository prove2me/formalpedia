-- Prove2me | solution 1 for AlgebraicCurve.Annulus.exists_band_dom_eq_and_param_eq_and_modulus_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c5f1a7c1-4632-50e4-892c-9e503ae10a1a

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_exists_band_dom_eq_and_param_eq_and_modulus_eq

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.GaussReduction AlgebraicCurve.StandardAnnulus

namespace SubBand

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem val_ne_zero_of_ne {x : L} (hx : x ≠ 0) : A.valuation x ≠ 0 := (map_ne_zero A.valuation).mpr hx

theorem val_pos_of_ne {x : L} (hx : x ≠ 0) : 0 < A.valuation x :=
  lt_of_le_of_ne zero_le' (val_ne_zero_of_ne hx).symm

theorem val_inv_mul_lt_one {x y : L} (hy : y ≠ 0) (h : A.valuation x < A.valuation y) :
    A.valuation (y⁻¹ * x) < 1 := by
  rw [map_mul, map_inv₀, inv_mul_lt_iff₀ (val_pos_of_ne hy), mul_one]
  exact h

theorem exists_mem_maximalIdeal_of_val_lt_one {x : L} (h : A.valuation x < 1) :
    ∃ hx : x ∈ A, (⟨x, hx⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
  ⟨(A.valuation_le_one_iff x).mp h.le, (A.valuation_lt_one_iff ⟨x, _⟩).mpr h⟩

theorem evalAt_inv_const_mul (P : Place L F) (hP : P.IsRational) (c : L) {z : F} (hz : z ∈ P.toValuationSubring) :
    P.evalAt ((algebraMap L F c)⁻¹ * z) = c⁻¹ * P.evalAt z := by
  rw [← map_inv₀, evalAt_mul_of_mem P hP (P.algebraMap_mem' _) hz, evalAt_algebraMap_const P hP]

theorem ord_eq_zero_of_mem_of_evalAt_ne_zero (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring)
    (hf0 : f ≠ 0) (h : P.evalAt f ≠ 0) : P.ord f = 0 := by
  have h0 := ord_nonneg_of_mem_gen P hf hf0
  by_contra hne
  exact h (evalAt_eq_zero_of_ord_pos P hf0 (by omega))

theorem ord_prod {ι : Type*} (P : Place L F) (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    P.ord (∏ i ∈ s, f i) = ∑ i ∈ s, P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Place.ord_mul _ (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem evalAt_prod {ι : Type*} (P : Place L F) (hP : P.IsRational) (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i ∈ P.toValuationSubring) :
    P.evalAt (∏ i ∈ s, f i) = ∏ i ∈ s, P.evalAt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.evalAt_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      evalAt_mul_of_mem P hP (hf a (Finset.mem_insert_self a s))
        (prod_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem evalAt_zpow_of_ord_eq_zero (P : Place L F) (hP : P.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : P.ord f = 0) (n : ℤ) : P.evalAt (f ^ n) = P.evalAt f ^ n := by
  have hmem : f ∈ P.toValuationSubring := mem_of_ord_nonneg_gen P hf0 h.ge
  have hpow : ∀ k : ℕ, P.evalAt (f ^ k) = P.evalAt f ^ k := by
    intro k
    induction k with
    | zero => simp [Place.evalAt_one]
    | succ k ih => rw [pow_succ, pow_succ, evalAt_mul_of_mem P hP (pow_mem hmem k) hmem, ih]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast, hpow]
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow,
      ← evalAt_inv_of_ord_eq_zero P hP hf0 h]
    have hmem' : f⁻¹ ∈ P.toValuationSubring :=
      mem_of_ord_nonneg_gen P (inv_ne_zero hf0) (by rw [Place.ord_inv]; omega)
    induction k with
    | zero => simp [Place.evalAt_one]
    | succ k ih => rw [pow_succ, pow_succ, evalAt_mul_of_mem P hP (pow_mem hmem' k) hmem', ih]

theorem zpow_mem_of_ord_eq_zero (P : Place L F) {f : F} (hf0 : f ≠ 0) (h : P.ord f = 0) (n : ℤ) :
    f ^ n ∈ P.toValuationSubring :=
  mem_of_ord_nonneg_gen P (zpow_ne_zero n hf0) (by rw [Place.ord_zpow, h, mul_zero])

theorem prod_zpow_eq_zpow_sum {ι : Type*} (x : L) (hx : x ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    ∏ i ∈ s, x ^ e i = x ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

theorem val_sub_eq_left {x y : L} (h : A.valuation y < A.valuation x) : A.valuation (x - y) = A.valuation x := by
  rw [sub_eq_add_neg]
  exact Valuation.map_add_eq_of_lt_left _ (by rwa [Valuation.map_neg])

theorem val_sub_eq_right {x y : L} (h : A.valuation x < A.valuation y) : A.valuation (x - y) = A.valuation y := by
  rw [sub_eq_add_neg, ← Valuation.map_neg _ y]
  exact Valuation.map_add_eq_of_lt_right _ (by rwa [Valuation.map_neg])

theorem val_eq_one_of_isUnit {x : L} (hx : x ∈ A) (h : IsUnit (⟨x, hx⟩ : A)) : A.valuation x = 1 :=
  (A.valuation_eq_one_iff ⟨x, hx⟩).mp h

theorem key_identity (fP a c zP Pin Pout Zout : L) (k S : ℤ)
    (ha : a ≠ 0) (hc : c ≠ 0) (hz : zP ≠ 0) (hPin : Pin ≠ 0) (hPout : Pout ≠ 0) (hZ : Zout ≠ 0) :
    fP * (a * Zout * c ^ (k + S))⁻¹ * (c⁻¹ * zP) ^ (-(k + S)) =
      (fP * (Pin * Pout)⁻¹ * a⁻¹ * zP ^ (-k)) * (Pin * zP ^ (-S)) * (Pout * Zout⁻¹) := by
  rw [mul_zpow, inv_zpow', neg_neg, show -(k + S) = -k + -S by ring, zpow_add₀ hz]
  have h1 : c ^ (k + S) ≠ 0 := zpow_ne_zero _ hc
  have h2 : zP ^ (-k) ≠ 0 := zpow_ne_zero _ hz
  have h3 : zP ^ (-S) ≠ 0 := zpow_ne_zero _ hz
  field_simp

section Ann

variable (An : Annulus A F)

theorem eq_of_evalAt_param_eq {P R : Place L F} (hP : P ∈ An.dom) (hR : R ∈ An.dom)
    (h : P.evalAt An.param = R.evalAt An.param) : P = R := by
  obtain ⟨_, _, ⟨hzA, hzmax⟩, hz0, m, hm, hmeq⟩ := An.mem_dom P hP
  obtain ⟨Q, _, huniq⟩ := An.existsUnique_evalAt_eq ⟨P.evalAt An.param, hzA⟩ hzmax hz0 ⟨m, hm, hmeq⟩
  exact (huniq P ⟨hP, rfl⟩).trans (huniq R ⟨hR, h.symm⟩).symm

theorem param_sub_ne_zero {R : Place L F} (hR : R ∈ An.dom) :
    An.param - algebraMap L F (R.evalAt An.param) ≠ 0 := by
  intro h0
  have h1 := An.ord_param_sub R hR
  rw [h0, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem evalAt_param_sub {P R : Place L F} (hP : P ∈ An.dom) :
    P.evalAt (An.param - algebraMap L F (R.evalAt An.param)) = P.evalAt An.param - R.evalAt An.param := by
  obtain ⟨hrat, hzmem, -⟩ := An.mem_dom P hP
  rw [evalAt_sub_of_mem P hrat hzmem (P.algebraMap_mem' _), evalAt_algebraMap_const P hrat]

theorem ord_param_sub_eq [DecidableEq (Place L F)] {P R : Place L F} (hP : P ∈ An.dom) (hR : R ∈ An.dom) :
    P.ord (An.param - algebraMap L F (R.evalAt An.param)) = if P = R then 1 else 0 := by
  split_ifs with h
  · subst h; exact An.ord_param_sub P hP
  · obtain ⟨hrat, hzmem, -⟩ := An.mem_dom P hP
    apply ord_eq_zero_of_mem_of_evalAt_ne_zero P (sub_mem hzmem (P.algebraMap_mem' _)) (param_sub_ne_zero An hR)
    rw [evalAt_param_sub An hP]
    exact fun h0 => h (eq_of_evalAt_param_eq An hP hR (sub_eq_zero.mp h0))

variable [HasPrincipalDivisors L F]

theorem exists_factor (f : F) (hf0 : f ≠ 0) :
    ∃ T : Finset (Place L F), (∀ R ∈ T, R ∈ An.dom) ∧ (∀ P ∈ An.dom, P.ord f ≠ 0 → P ∈ T) ∧
      (∀ R ∈ T, R.ord f ≠ 0) ∧
      (f * ∏ R ∈ T, (An.param - algebraMap L F (R.evalAt An.param)) ^ (-R.ord f)) ≠ 0 ∧
      ∀ P ∈ An.dom, P.ord (f * ∏ R ∈ T, (An.param - algebraMap L F (R.evalAt An.param)) ^ (-R.ord f)) = 0 := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) f hf0
  refine ⟨D.support.filter fun R => R ∈ An.dom, fun R hR => (Finset.mem_filter.mp hR).2,
    fun P hP hPf => Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hD]; exact hPf), hP⟩,
    fun R hR => by have h := Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hR).1; rwa [hD] at h, ?_, ?_⟩
  · exact mul_ne_zero hf0 (Finset.prod_ne_zero_iff.mpr fun R hR =>
      zpow_ne_zero _ (param_sub_ne_zero An (Finset.mem_filter.mp hR).2))
  · intro P hP
    rw [Place.ord_mul _ hf0 (Finset.prod_ne_zero_iff.mpr fun R hR =>
      zpow_ne_zero _ (param_sub_ne_zero An (Finset.mem_filter.mp hR).2)),
      ord_prod P _ _ fun R hR => zpow_ne_zero _ (param_sub_ne_zero An (Finset.mem_filter.mp hR).2)]
    simp_rw [Place.ord_zpow]
    by_cases hPT : P ∈ D.support.filter fun R => R ∈ An.dom
    · rw [Finset.sum_eq_single_of_mem P hPT]
      · rw [ord_param_sub_eq An hP hP, if_pos rfl]; ring
      · intro R hR hRP
        rw [ord_param_sub_eq An hP (Finset.mem_filter.mp hR).2, if_neg (Ne.symm hRP), mul_zero]
    · have hordP : P.ord f = 0 := by
        by_contra hne
        exact hPT (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by rw [hD]; exact hne), hP⟩)
      rw [hordP, zero_add]
      refine Finset.sum_eq_zero fun R hR => ?_
      rw [ord_param_sub_eq An hP (Finset.mem_filter.mp hR).2, if_neg (fun h : P = R => hPT (h.symm ▸ hR)), mul_zero]

end Ann

end SubBand

open SubBand in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    (An : Annulus A F) (b c : L) (t : A)
    (hc : A.valuation c ≤ 1) (hc0 : c ≠ 0) (ht : t ∈ IsLocalRing.maximalIdeal A) (ht0 : (t : L) ≠ 0)
    (hb : A.valuation (c * (t : L)) = A.valuation b)
    (hmod : A.valuation ((An.modulus : A) : L) ≤ A.valuation (c * (t : L))) :
    ∃ B : Annulus A F,
      B.dom = {P | P ∈ An.dom ∧ A.valuation b < A.valuation (P.evalAt An.param) ∧
        A.valuation (P.evalAt An.param) < A.valuation c} ∧
      B.param = (algebraMap L F c)⁻¹ * An.param ∧
      B.modulus = t := by
  classical
  have htv : A.valuation (t : L) < 1 := (A.valuation_lt_one_iff t).mp ht
  have hcv0 : A.valuation c ≠ 0 := val_ne_zero_of_ne hc0
  refine ⟨{ dom := {P | P ∈ An.dom ∧ A.valuation b < A.valuation (P.evalAt An.param) ∧
              A.valuation (P.evalAt An.param) < A.valuation c}
            param := (algebraMap L F c)⁻¹ * An.param
            modulus := t
            modulus_mem := ht
            mem_dom := ?_
            existsUnique_evalAt_eq := ?_
            ord_param_sub := ?_
            unit_principle := ?_ }, rfl, rfl, rfl⟩
  ·
    rintro P ⟨hPdom, hbP, hPc⟩
    obtain ⟨hrat, hzmem, ⟨hzA, hzmax⟩, hz0, m, hm, hmod_eq⟩ := An.mem_dom P hPdom
    have hev : P.evalAt ((algebraMap L F c)⁻¹ * An.param) = c⁻¹ * P.evalAt An.param :=
      evalAt_inv_const_mul P hrat c hzmem
    refine ⟨hrat, by rw [← map_inv₀]; exact mul_mem (P.algebraMap_mem' _) hzmem, ?_, ?_, ?_⟩
    · rw [hev]
      exact exists_mem_maximalIdeal_of_val_lt_one (val_inv_mul_lt_one hc0 hPc)
    · rw [hev]
      exact mul_ne_zero (inv_ne_zero hc0) hz0
    · rw [hev]
      have hm'v : A.valuation ((P.evalAt An.param)⁻¹ * (c * (t : L))) < 1 :=
        val_inv_mul_lt_one hz0 (by rw [hb]; exact hbP)
      obtain ⟨hm'A, hm'max⟩ := exists_mem_maximalIdeal_of_val_lt_one hm'v
      refine ⟨⟨_, hm'A⟩, hm'max, ?_⟩
      show (t : L) = c⁻¹ * P.evalAt An.param * ((P.evalAt An.param)⁻¹ * (c * (t : L)))
      field_simp
  ·
    intro c' hc' hc'0 hm
    obtain ⟨m, hm, hmt⟩ := hm
    have hc'v : A.valuation (c' : L) < 1 := (A.valuation_lt_one_iff c').mp hc'
    have hmv : A.valuation (m : L) < 1 := (A.valuation_lt_one_iff m).mp hm
    have hcc0 : c * (c' : L) ≠ 0 := mul_ne_zero hc0 hc'0
    have hccv : A.valuation (c * (c' : L)) < A.valuation c := by
      rw [map_mul]
      calc A.valuation c * A.valuation (c' : L) < A.valuation c * 1 :=
            mul_lt_mul_of_pos_left hc'v (val_pos_of_ne hc0)
        _ = A.valuation c := mul_one _
    have hccv1 : A.valuation (c * (c' : L)) < 1 := lt_of_lt_of_le hccv hc
    obtain ⟨hccA, hccmax⟩ := exists_mem_maximalIdeal_of_val_lt_one hccv1

    have hbcc : A.valuation b < A.valuation (c * (c' : L)) := by
      rw [← hb, hmt, ← mul_assoc, map_mul (A.valuation) (c * (c' : L))]
      calc A.valuation (c * (c' : L)) * A.valuation (m : L) < A.valuation (c * (c' : L)) * 1 :=
            mul_lt_mul_of_pos_left hmv (val_pos_of_ne hcc0)
        _ = A.valuation (c * (c' : L)) := mul_one _
    have hmod' : ∃ m' ∈ IsLocalRing.maximalIdeal A, ((An.modulus : A) : L) = c * (c' : L) * (m' : L) := by
      have hv : A.valuation ((c * (c' : L))⁻¹ * ((An.modulus : A) : L)) < 1 :=
        val_inv_mul_lt_one hcc0 (lt_of_le_of_lt hmod (hb ▸ hbcc))
      obtain ⟨hA', hmax'⟩ := exists_mem_maximalIdeal_of_val_lt_one hv
      refine ⟨⟨_, hA'⟩, hmax', ?_⟩
      show ((An.modulus : A) : L) = c * (c' : L) * ((c * (c' : L))⁻¹ * ((An.modulus : A) : L))
      field_simp
    obtain ⟨P, ⟨hPdom, hPz⟩, huniq⟩ := An.existsUnique_evalAt_eq ⟨c * (c' : L), hccA⟩ hccmax hcc0 hmod'
    have hPz' : P.evalAt An.param = c * (c' : L) := hPz
    obtain ⟨hrat, hzmem, -⟩ := An.mem_dom P hPdom
    refine ⟨P, ⟨⟨hPdom, ?_, ?_⟩, ?_⟩, ?_⟩
    · rw [hPz']; exact hbcc
    · rw [hPz']; exact hccv
    · show P.evalAt ((algebraMap L F c)⁻¹ * An.param) = (c' : L)
      rw [evalAt_inv_const_mul P hrat c hzmem, hPz', ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    · rintro Q ⟨⟨hQdom, -, -⟩, hQz⟩
      obtain ⟨hQrat, hQzmem, -⟩ := An.mem_dom Q hQdom
      have hQz' : Q.evalAt An.param = c * (c' : L) := by
        have h := hQz
        change Q.evalAt ((algebraMap L F c)⁻¹ * An.param) = (c' : L) at h
        rw [evalAt_inv_const_mul Q hQrat c hQzmem] at h
        rw [← h, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      exact huniq Q ⟨hQdom, hQz'⟩
  ·
    rintro P ⟨hPdom, -, -⟩
    obtain ⟨hrat, hzmem, -⟩ := An.mem_dom P hPdom
    show P.ord ((algebraMap L F c)⁻¹ * An.param - algebraMap L F (P.evalAt ((algebraMap L F c)⁻¹ * An.param))) = 1
    rw [evalAt_inv_const_mul P hrat c hzmem]
    have hfac : (algebraMap L F c)⁻¹ * An.param - algebraMap L F (c⁻¹ * P.evalAt An.param) =
        (algebraMap L F c)⁻¹ * (An.param - algebraMap L F (P.evalAt An.param)) := by
      rw [map_mul, map_inv₀, mul_sub]
    rw [hfac, Place.ord_mul _ (inv_ne_zero ((map_ne_zero _).mpr hc0)) (param_sub_ne_zero An hPdom),
      Place.ord_inv, ord_algebraMap_eq_zero _ hc0, An.ord_param_sub P hPdom]
    simp
  ·
    intro f hf0 hordf
    obtain ⟨T, hTdom, hTzer, hTord, hg0, hordg⟩ := exists_factor An f hf0
    obtain ⟨k, a, ha0, hunit⟩ := An.unit_principle _ hg0 hordg

    refine ⟨k + ∑ R ∈ T.filter (fun R => A.valuation (R.evalAt An.param) ≤ A.valuation b), R.ord f,
      a * (∏ R ∈ T.filter (fun R => ¬ A.valuation (R.evalAt An.param) ≤ A.valuation b), R.evalAt An.param ^ R.ord f) *
        c ^ (k + ∑ R ∈ T.filter (fun R => A.valuation (R.evalAt An.param) ≤ A.valuation b), R.ord f), ?_, ?_⟩
    · refine mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ ?_)) (zpow_ne_zero _ hc0)
      exact (An.mem_dom R (hTdom R (Finset.mem_filter.mp hR).1)).2.2.2.1
    · rintro P ⟨hPdom, hbP, hPc⟩
      obtain ⟨hrat, hzmem, ⟨hzA, hzmax⟩, hz0, -, -, -⟩ := An.mem_dom P hPdom
      have hordfP : P.ord f = 0 := hordf P ⟨hPdom, hbP, hPc⟩

      have hToff : ∀ R ∈ T, A.valuation (R.evalAt An.param) ≤ A.valuation b ∨
          A.valuation c ≤ A.valuation (R.evalAt An.param) := by
        intro R hR
        by_contra hcon
        simp only [not_or, not_le] at hcon
        exact hTord R hR (hordf R ⟨hTdom R hR, hcon.1, hcon.2⟩)
      have hPT : ∀ R ∈ T, P ≠ R := by
        intro R hR hPR; subst hPR; exact hTord P hR hordfP
      have hzR0 : ∀ R ∈ T, R.evalAt An.param ≠ 0 := fun R hR => (An.mem_dom R (hTdom R hR)).2.2.2.1
      have hsub0 : ∀ R ∈ T, P.evalAt An.param - R.evalAt An.param ≠ 0 :=
        fun R hR h0 => hPT R hR (eq_of_evalAt_param_eq An hPdom (hTdom R hR) (sub_eq_zero.mp h0))
      have hordsub : ∀ R ∈ T, P.ord (An.param - algebraMap L F (R.evalAt An.param)) = 0 := by
        intro R hR; rw [ord_param_sub_eq An hPdom (hTdom R hR), if_neg (hPT R hR)]

      obtain ⟨hgA, hgunit⟩ := hunit P hPdom
      have hgval : P.evalAt (f * ∏ R ∈ T, (An.param - algebraMap L F (R.evalAt An.param)) ^ (-R.ord f)) =
          P.evalAt f * ∏ R ∈ T, (P.evalAt An.param - R.evalAt An.param) ^ (-R.ord f) := by
        rw [evalAt_mul_of_mem P hrat (mem_of_ord_nonneg_gen P hf0 hordfP.ge)
          (prod_mem fun R hR => zpow_mem_of_ord_eq_zero P (param_sub_ne_zero An (hTdom R hR)) (hordsub R hR) _),
          evalAt_prod P hrat _ _ fun R hR => zpow_mem_of_ord_eq_zero P (param_sub_ne_zero An (hTdom R hR)) (hordsub R hR) _]
        congr 1
        refine Finset.prod_congr rfl fun R hR => ?_
        rw [evalAt_zpow_of_ord_eq_zero P hrat (param_sub_ne_zero An (hTdom R hR)) (hordsub R hR), evalAt_param_sub An hPdom]
      have hU0 := val_eq_one_of_isUnit _ hgunit
      rw [hgval] at hU0

      set zP := P.evalAt An.param with hzP
      set Tin := T.filter (fun R => A.valuation (R.evalAt An.param) ≤ A.valuation b) with hTin
      set Tout := T.filter (fun R => ¬ A.valuation (R.evalAt An.param) ≤ A.valuation b) with hTout
      set S := ∑ R ∈ Tin, R.ord f with hS
      set Zout := ∏ R ∈ Tout, R.evalAt An.param ^ R.ord f with hZout
      have hTinT : ∀ R ∈ Tin, R ∈ T := fun R hR => (Finset.mem_filter.mp hR).1
      have hToutT : ∀ R ∈ Tout, R ∈ T := fun R hR => (Finset.mem_filter.mp hR).1
      have hPin0 : (∏ R ∈ Tin, (zP - R.evalAt An.param) ^ R.ord f) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ (hsub0 R (hTinT R hR))
      have hPout0 : (∏ R ∈ Tout, (zP - R.evalAt An.param) ^ R.ord f) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ (hsub0 R (hToutT R hR))
      have hZout0 : Zout ≠ 0 := Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ (hzR0 R (hToutT R hR))

      have hPneg : (∏ R ∈ T, (zP - R.evalAt An.param) ^ (-R.ord f)) =
          ((∏ R ∈ Tin, (zP - R.evalAt An.param) ^ R.ord f) * ∏ R ∈ Tout, (zP - R.evalAt An.param) ^ R.ord f)⁻¹ := by
        rw [hTin, hTout, Finset.prod_filter_mul_prod_filter_not, ← Finset.prod_inv_distrib]
        exact Finset.prod_congr rfl fun R _ => zpow_neg _ _

      have hWin : ∀ R ∈ Tin, A.valuation (((zP - R.evalAt An.param) * zP⁻¹) ^ R.ord f) = 1 := by
        intro R hR
        obtain ⟨hRT, hRin⟩ := Finset.mem_filter.mp hR
        rw [map_zpow₀, map_mul, map_inv₀, val_sub_eq_left (lt_of_le_of_lt hRin hbP),
          mul_inv_cancel₀ (val_ne_zero_of_ne hz0), one_zpow]
      have hWout : ∀ R ∈ Tout, A.valuation (((zP - R.evalAt An.param) * (R.evalAt An.param)⁻¹) ^ R.ord f) = 1 := by
        intro R hR
        obtain ⟨hRT, hRout⟩ := Finset.mem_filter.mp hR
        have hcR : A.valuation c ≤ A.valuation (R.evalAt An.param) := (hToff R hRT).resolve_left hRout
        rw [map_zpow₀, map_mul, map_inv₀, val_sub_eq_right (lt_of_lt_of_le hPc hcR),
          mul_inv_cancel₀ (val_ne_zero_of_ne (hzR0 R hRT)), one_zpow]

      have hii : ∏ R ∈ Tin, ((zP - R.evalAt An.param) * zP⁻¹) ^ R.ord f =
          (∏ R ∈ Tin, (zP - R.evalAt An.param) ^ R.ord f) * zP ^ (-S) := by
        rw [hS, ← Finset.sum_neg_distrib, ← prod_zpow_eq_zpow_sum zP hz0, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun R _ => by rw [mul_zpow, inv_zpow']
      have hiii : ∏ R ∈ Tout, ((zP - R.evalAt An.param) * (R.evalAt An.param)⁻¹) ^ R.ord f =
          (∏ R ∈ Tout, (zP - R.evalAt An.param) ^ R.ord f) * Zout⁻¹ := by
        rw [hZout, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun R _ => by rw [mul_zpow, inv_zpow]

      have hval : A.valuation (P.evalAt f * (a * Zout * c ^ (k + S))⁻¹ *
          (P.evalAt ((algebraMap L F c)⁻¹ * An.param)) ^ (-(k + S))) = 1 := by
        rw [evalAt_inv_const_mul P hrat c hzmem, ← hzP,
          key_identity (P.evalAt f) a c zP _ _ Zout k S ha0 hc0 hz0 hPin0 hPout0 hZout0,
          ← hPneg, ← hii, ← hiii, map_mul, map_mul, hU0, map_prod, map_prod,
          Finset.prod_eq_one hWin, Finset.prod_eq_one hWout, one_mul, one_mul]
      exact exists_isUnit_of_valuation_eq_one A hval

end S_AlgebraicCurve_Annulus_exists_band_dom_eq_and_param_eq_and_modulus_eq
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_exists_band_dom_eq_and_param_eq_and_modulus_eq (solution)
