-- Prove2me | solution 1 for AlgebraicCurve.Annulus.IsAttached.of_param_eq_of_forall_mem_dom_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/61f1f445-0be8-52f0-8d04-004c14b15724

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff

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

theorem prod_zpow_eq_zpow_sum₀ {M : Type*} [CommGroupWithZero M] {ι : Type*} (x : M) (hx : x ≠ 0)
    (s : Finset ι) (e : ι → ℤ) : ∏ i ∈ s, x ^ e i = x ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

section Chart

variable {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb] (C : ComponentChart A F Fb)

theorem inv_mem_integers_of_residue_ne_zero {y : F} (hy : y ∈ C.integers) (h : C.residue ⟨y, hy⟩ ≠ 0) :
    y⁻¹ ∈ C.integers := by
  have hnm : (⟨y, hy⟩ : C.integers) ∉ IsLocalRing.maximalIdeal C.integers := by
    rw [← C.ker_residue, RingHom.mem_ker]
    exact h
  have hu : IsUnit (⟨y, hy⟩ : C.integers) := by
    by_contra hnu
    exact hnm ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu))
  obtain ⟨u, hu⟩ := hu
  have hy0 : y ≠ 0 := by
    intro h0
    apply h
    have : (⟨y, hy⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hinv : ((u⁻¹ : (C.integers)ˣ) : C.integers) * ⟨y, hy⟩ = 1 := by rw [← hu, Units.inv_mul]
  have hval : (((u⁻¹ : (C.integers)ˣ) : C.integers) : F) = y⁻¹ := by
    have h2 := congrArg (fun w : C.integers => (w : F)) hinv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h2
    exact (eq_inv_of_mul_eq_one_left h2)
  rw [← hval]
  exact ((u⁻¹ : (C.integers)ˣ) : C.integers).2

theorem zpow_mem_integers {y : F} (hy : y ∈ C.integers) (hy' : y⁻¹ ∈ C.integers) (n : ℤ) :
    y ^ n ∈ C.integers := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast]; exact pow_mem hy k
  · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem hy' k

theorem residue_zpow {y : F} (hy : y ∈ C.integers) (hy' : y⁻¹ ∈ C.integers) (hy0 : y ≠ 0) (n : ℤ) :
    C.residue ⟨y ^ n, zpow_mem_integers C hy hy' n⟩ = C.residue ⟨y, hy⟩ ^ n := by
  have hpow : ∀ (w : F) (hw : w ∈ C.integers) (k : ℕ),
      C.residue ⟨w ^ k, pow_mem hw k⟩ = C.residue ⟨w, hw⟩ ^ k := by
    intro w hw k
    rw [← map_pow]
    congr 1
  have hinvres : C.residue ⟨y⁻¹, hy'⟩ = (C.residue ⟨y, hy⟩)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← map_mul]
    have : (⟨y, hy⟩ : C.integers) * ⟨y⁻¹, hy'⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hy0)
    rw [this, map_one]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · have : (⟨y ^ (k : ℤ), zpow_mem_integers C hy hy' k⟩ : C.integers) = ⟨y ^ k, pow_mem hy k⟩ :=
      Subtype.ext (show y ^ (k : ℤ) = y ^ k from zpow_natCast y k)
    rw [this, hpow y hy, zpow_natCast]
  · have : (⟨y ^ (-(k : ℤ)), zpow_mem_integers C hy hy' _⟩ : C.integers) = ⟨y⁻¹ ^ k, pow_mem hy' k⟩ :=
      Subtype.ext (show y ^ (-(k : ℤ)) = y⁻¹ ^ k by rw [zpow_neg, zpow_natCast, inv_pow])
    rw [this, hpow y⁻¹ hy', hinvres, zpow_neg, zpow_natCast, inv_pow]

theorem residue_prod {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ∈ C.integers) :
    C.residue ⟨∏ i ∈ s, f i, prod_mem hf⟩ = ∏ i ∈ s.attach, C.residue ⟨f i, hf i i.2⟩ := by
  classical
  have : (⟨∏ i ∈ s, f i, prod_mem hf⟩ : C.integers) = ∏ i ∈ s.attach, (⟨f i, hf i i.2⟩ : C.integers) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_finsetProd]
    exact (Finset.prod_attach s f).symm
  rw [this, map_prod]

end Chart

end SubBand

open SubBand in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (An₀ : Annulus A F) (C : ComponentChart A F Fb) (x : Place (IsLocalRing.ResidueField ↥A) Fb)
    (hatt : An₀.IsAttached C x)
    (B : Annulus A F) (hparam : B.param = An₀.param)
    (b : L) (hdom : ∀ P, P ∈ B.dom ↔ P ∈ An₀.dom ∧ A.valuation b < A.valuation (P.evalAt An₀.param)) :
    B.IsAttached C x := by
  classical
  obtain ⟨hx, hz, hzord, hlaw⟩ := hatt
  have hzB : B.param ∈ C.integers := by rw [hparam]; exact hz
  have hBz : (⟨B.param, hzB⟩ : C.integers) = ⟨An₀.param, hz⟩ := Subtype.ext hparam
  refine ⟨hx, hzB, by rw [hBz]; exact hzord, ?_⟩
  intro f hf hres hordf P hPB
  rw [hparam]
  obtain ⟨hPdom, hbP⟩ := (hdom P).mp hPB
  obtain ⟨hrat, hzmem, ⟨hzA, hzmax⟩, hz0, -, -, -⟩ := An₀.mem_dom P hPdom
  have hf0 : f ≠ 0 := by
    intro h0; apply hres
    have : (⟨f, hf⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hzbar0 : C.residue ⟨An₀.param, hz⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzord; exact zero_ne_one hzord

  obtain ⟨T, hTdom, hTzer, hTord, hg0, hordg⟩ := exists_factor An₀ f hf0
  have hordfP : P.ord f = 0 := hordf P hPB

  have hTdeep : ∀ R ∈ T, A.valuation (R.evalAt An₀.param) < A.valuation (P.evalAt An₀.param) := by
    intro R hR
    have hRB : R ∉ B.dom := fun h => hTord R hR (hordf R h)
    have : ¬ A.valuation b < A.valuation (R.evalAt An₀.param) := fun h => hRB ((hdom R).mpr ⟨hTdom R hR, h⟩)
    exact lt_of_le_of_lt (not_lt.mp this) hbP
  have hPT : ∀ R ∈ T, P ≠ R := by
    intro R hR hPR; subst hPR; exact hTord P hR hordfP
  have hsub0 : ∀ R ∈ T, P.evalAt An₀.param - R.evalAt An₀.param ≠ 0 :=
    fun R hR h0 => hPT R hR (eq_of_evalAt_param_eq An₀ hPdom (hTdom R hR) (sub_eq_zero.mp h0))
  have hordsub : ∀ R ∈ T, P.ord (An₀.param - algebraMap L F (R.evalAt An₀.param)) = 0 := by
    intro R hR; rw [ord_param_sub_eq An₀ hPdom (hTdom R hR), if_neg (hPT R hR)]

  have hzRA : ∀ R ∈ T, R.evalAt An₀.param ∈ A := fun R hR => (An₀.mem_dom R (hTdom R hR)).2.2.1.1
  have hzRmax : ∀ R (hR : R ∈ T), (⟨R.evalAt An₀.param, hzRA R hR⟩ : A) ∈ IsLocalRing.maximalIdeal A :=
    fun R hR => (An₀.mem_dom R (hTdom R hR)).2.2.1.2
  have hfacmem : ∀ R ∈ T, An₀.param - algebraMap L F (R.evalAt An₀.param) ∈ C.integers :=
    fun R hR => sub_mem hz ((C.algebraMap_mem_iff _).mpr (hzRA R hR))
  have hfacres : ∀ R (hR : R ∈ T), C.residue ⟨An₀.param - algebraMap L F (R.evalAt An₀.param), hfacmem R hR⟩ =
      C.residue ⟨An₀.param, hz⟩ := by
    intro R hR
    have hsplit : (⟨An₀.param - algebraMap L F (R.evalAt An₀.param), hfacmem R hR⟩ : C.integers) =
        ⟨An₀.param, hz⟩ - ⟨algebraMap L F ((⟨R.evalAt An₀.param, hzRA R hR⟩ : A) : L),
          (C.algebraMap_mem_iff _).mpr (hzRA R hR)⟩ := Subtype.ext rfl
    rw [hsplit, map_sub, C.residue_algebraMap ⟨R.evalAt An₀.param, hzRA R hR⟩,
      (IsLocalRing.residue_eq_zero_iff _).mpr (hzRmax R hR), map_zero, sub_zero]
  have hfacres0 : ∀ R (hR : R ∈ T), C.residue ⟨An₀.param - algebraMap L F (R.evalAt An₀.param), hfacmem R hR⟩ ≠ 0 :=
    fun R hR => by rw [hfacres R hR]; exact hzbar0
  have hfacinv : ∀ R ∈ T, (An₀.param - algebraMap L F (R.evalAt An₀.param))⁻¹ ∈ C.integers :=
    fun R hR => inv_mem_integers_of_residue_ne_zero C (hfacmem R hR) (hfacres0 R hR)

  have hprodmem : ∀ R ∈ T, (An₀.param - algebraMap L F (R.evalAt An₀.param)) ^ (-R.ord f) ∈ C.integers :=
    fun R hR => zpow_mem_integers C (hfacmem R hR) (hfacinv R hR) _
  have hgmem : f * ∏ R ∈ T, (An₀.param - algebraMap L F (R.evalAt An₀.param)) ^ (-R.ord f) ∈ C.integers :=
    mul_mem hf (prod_mem hprodmem)
  set S : ℤ := ∑ R ∈ T, R.ord f with hS
  have hgres : C.residue ⟨_, hgmem⟩ = C.residue ⟨f, hf⟩ * C.residue ⟨An₀.param, hz⟩ ^ (-S) := by
    have hsplit : (⟨_, hgmem⟩ : C.integers) = ⟨f, hf⟩ * ⟨_, prod_mem hprodmem⟩ := Subtype.ext rfl
    rw [hsplit, map_mul, residue_prod C T _ hprodmem]
    congr 1
    rw [hS, ← Finset.sum_neg_distrib, ← prod_zpow_eq_zpow_sum₀ _ hzbar0, ← Finset.prod_attach T (fun R => C.residue ⟨An₀.param, hz⟩ ^ (-R.ord f))]
    refine Finset.prod_congr rfl fun R _ => ?_
    rw [residue_zpow C (hfacmem R R.2) (hfacinv R R.2) (param_sub_ne_zero An₀ (hTdom R R.2)), hfacres R R.2]
  have hgres0 : C.residue ⟨_, hgmem⟩ ≠ 0 := by
    rw [hgres]; exact mul_ne_zero hres (zpow_ne_zero _ hzbar0)
  have hgord : x.ord (C.residue ⟨_, hgmem⟩) = x.ord (C.residue ⟨f, hf⟩) - S := by
    rw [hgres, Place.ord_mul _ hres (zpow_ne_zero _ hzbar0), Place.ord_zpow, hzord]; ring

  obtain ⟨hgA, hgunit⟩ := hlaw _ hgmem hgres0 hordg P hPdom
  have hU := val_eq_one_of_isUnit _ hgunit
  rw [hgord] at hU

  have hgval : P.evalAt (f * ∏ R ∈ T, (An₀.param - algebraMap L F (R.evalAt An₀.param)) ^ (-R.ord f)) =
      P.evalAt f * ∏ R ∈ T, (P.evalAt An₀.param - R.evalAt An₀.param) ^ (-R.ord f) := by
    rw [evalAt_mul_of_mem P hrat (mem_of_ord_nonneg_gen P hf0 hordfP.ge)
      (prod_mem fun R hR => zpow_mem_of_ord_eq_zero P (param_sub_ne_zero An₀ (hTdom R hR)) (hordsub R hR) _),
      evalAt_prod P hrat _ _ fun R hR => zpow_mem_of_ord_eq_zero P (param_sub_ne_zero An₀ (hTdom R hR)) (hordsub R hR) _]
    congr 1
    refine Finset.prod_congr rfl fun R hR => ?_
    rw [evalAt_zpow_of_ord_eq_zero P hrat (param_sub_ne_zero An₀ (hTdom R hR)) (hordsub R hR), evalAt_param_sub An₀ hPdom]
  rw [hgval] at hU
  set zP := P.evalAt An₀.param with hzP

  have hPneg0 : (∏ R ∈ T, (zP - R.evalAt An₀.param) ^ (-R.ord f)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun R hR => zpow_ne_zero _ (hsub0 R hR)
  have hPnegval : A.valuation (∏ R ∈ T, (zP - R.evalAt An₀.param) ^ (-R.ord f)) = A.valuation zP ^ (-S) := by
    rw [map_prod, hS, ← Finset.sum_neg_distrib, ← prod_zpow_eq_zpow_sum₀ _ (val_ne_zero_of_ne hz0)]
    refine Finset.prod_congr rfl fun R hR => ?_
    rw [map_zpow₀, val_sub_eq_left (hTdeep R hR)]

  have hid : P.evalAt f * zP ^ (-(x.ord (C.residue ⟨f, hf⟩))) =
      (P.evalAt f * (∏ R ∈ T, (zP - R.evalAt An₀.param) ^ (-R.ord f)) * zP ^ (-(x.ord (C.residue ⟨f, hf⟩) - S))) *
        ((∏ R ∈ T, (zP - R.evalAt An₀.param) ^ (-R.ord f))⁻¹ * zP ^ (-S)) := by
    rw [show -(x.ord (C.residue ⟨f, hf⟩) - S) = -(x.ord (C.residue ⟨f, hf⟩)) + S by ring, zpow_add₀ hz0]
    have h1 : zP ^ (-(x.ord (C.residue ⟨f, hf⟩))) ≠ 0 := zpow_ne_zero _ hz0
    have h2 : zP ^ S ≠ 0 := zpow_ne_zero _ hz0
    have h3 : zP ^ (-S) = (zP ^ S)⁻¹ := zpow_neg _ _
    rw [h3]
    field_simp
  have hval : A.valuation (P.evalAt f * zP ^ (-(x.ord (C.residue ⟨f, hf⟩)))) = 1 := by
    rw [hid, map_mul, hU, one_mul, map_mul, map_inv₀, hPnegval, map_zpow₀]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (val_ne_zero_of_ne hz0))
  exact exists_isUnit_of_valuation_eq_one A hval

end S_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_IsAttached_of_param_eq_of_forall_mem_dom_iff (solution)
