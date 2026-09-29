-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.mapDomain_eq_ord_div_map_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a74e09d6-b5f3-5bf5-9dd4-e851264f2305

import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false

open Polynomial AlgebraicCurve AlgebraicCurve.RationalFunctionField

namespace Ws14Port

theorem ValuationSubring.inv_mem_maximalIdeal_of_not_mem {L : Type*} [Field L]
    {A : ValuationSubring L} {β : L} (hβ : β ∉ A) :
    ∃ h : β⁻¹ ∈ A, (⟨β⁻¹, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have hβ0 : β ≠ 0 := fun h => hβ (h ▸ A.zero_mem)
  have hv : 1 < A.valuation β := by
    rw [← not_le, A.valuation_le_one_iff]
    exact hβ
  have hvinv : A.valuation β⁻¹ < 1 := (A.valuation.one_lt_val_iff hβ0).mp hv
  refine ⟨(A.valuation_le_one_iff _).mp hvinv.le, ?_⟩
  rw [A.valuation_lt_one_iff]
  exact hvinv

theorem mem_of_mem_roots_map_of_monic {L : Type*} [Field L] {A : ValuationSubring L}
    {P : Polynomial A} (hP : P.Monic) {r : L}
    (hr : r ∈ (P.map (algebraMap A L)).roots) : r ∈ A := by
  have hint : IsIntegral A r := by
    refine ⟨P, hP, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    exact (Polynomial.mem_roots'.mp hr).2
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hs]
  exact s.2

theorem exists_multiset_map_monic_eq_prod {L : Type*} [Field L] [IsAlgClosed L]
    {A : ValuationSubring L} {P : Polynomial A} (hP : P.Monic) :
    ∃ s : Multiset A, s.map (algebraMap A L) = (P.map (algebraMap A L)).roots ∧
      P = (s.map fun t => Polynomial.X - Polynomial.C t).prod := by
  classical
  have hinj : Function.Injective (algebraMap A L) := fun x y h => Subtype.ext h
  have hfact : ((P.map (algebraMap A L)).roots.map
      fun t => Polynomial.X - Polynomial.C t).prod = P.map (algebraMap A L) :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
      (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  set s : Multiset A := ((P.map (algebraMap A L)).roots).attach.map
    (fun r => (⟨r.1, mem_of_mem_roots_map_of_monic hP r.2⟩ : A)) with hs
  have hsmap : s.map (algebraMap A L) = (P.map (algebraMap A L)).roots := by
    rw [hs, Multiset.map_map]
    conv_rhs => rw [← Multiset.attach_map_val ((P.map (algebraMap A L)).roots)]
    exact Multiset.map_congr rfl fun r _ => rfl
  refine ⟨s, hsmap, ?_⟩
  apply Polynomial.map_injective (algebraMap A L) hinj
  have hprodmap : (((s.map fun t => Polynomial.X - Polynomial.C t)).prod).map
      (algebraMap A L)
      = ((s.map fun t => Polynomial.X - Polynomial.C t).map
          (Polynomial.map (algebraMap A L))).prod := by
    rw [← Polynomial.coe_mapRingHom]
    exact map_multiset_prod (Polynomial.mapRingHom (algebraMap A L))
      (s.map fun t => Polynomial.X - Polynomial.C t)
  rw [hprodmap, Multiset.map_map,
    show (Polynomial.map (algebraMap A L) ∘ fun t : A => Polynomial.X - Polynomial.C t)
      = ((fun u : L => Polynomial.X - Polynomial.C u) ∘ (algebraMap A L)) from
      funext fun t => by simp [Polynomial.map_sub],
    ← Multiset.map_map, hsmap]
  exact hfact.symm

theorem map_red_eq_of_factorisation {L : Type*} [Field L] {A : ValuationSubring L} {k : Type*} [Field k]
    (red : A →+* k) (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    {P Pint Pout : Polynomial A} {c : A} (hfac : P = Polynomial.C c * Pint * Pout)
    (hPout : ∀ i : ℕ, Pout.coeff i - (if i = 0 then 1 else 0) ∈ IsLocalRing.maximalIdeal A) :
    P.map red = Polynomial.C (red c) * Pint.map red := by
  have hone : Pout.map red = 1 := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_one]
    have h := hred _ (hPout i)
    rw [map_sub, sub_eq_zero] at h
    rw [h]
    split_ifs <;> simp
  rw [hfac, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, hone, mul_one]

theorem red_ne_zero_of_not_mem {L : Type*} [Field L] {A : ValuationSubring L} {k : Type*} [Field k]
    (red : A →+* k) {c : A} (hc : c ∉ IsLocalRing.maximalIdeal A) : red c ≠ 0 := by
  have hu : IsUnit c := by
    by_contra h
    exact hc ((IsLocalRing.mem_maximalIdeal c).mpr h)
  exact (hu.map red).ne_zero

theorem exists_eq_C_mul_monic_mul_of_valuationSubring
    {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    (P : Polynomial A) :
    ∃ (c : A) (Pint Pout : Polynomial A),
      P = Polynomial.C c * Pint * Pout ∧
      Pint.Monic ∧
      (∀ i : ℕ, Pout.coeff i - (if i = 0 then 1 else 0) ∈ IsLocalRing.maximalIdeal A) ∧
      (∀ β ∈ (Pout.map (algebraMap A L)).roots, β ∉ A) ∧
      (c ∈ IsLocalRing.maximalIdeal A ↔ ∀ i, P.coeff i ∈ IsLocalRing.maximalIdeal A) := by
  classical
  have hinj : Function.Injective (algebraMap A L) := fun x y h => Subtype.ext h

  set R : Multiset L := (P.map (algebraMap A L)).roots with hRdef
  set Rin : Multiset L := R.filter (· ∈ A) with hRin
  set Rout : Multiset L := R.filter (fun a => ¬ a ∈ A) with hRout
  have hR : R = Rin + Rout := (Multiset.filter_add_not _ R).symm
  have hin : ∀ α ∈ Rin, α ∈ A := fun α hα => (Multiset.mem_filter.mp hα).2
  have hout : ∀ β ∈ Rout, β ∉ A := fun β hβ => (Multiset.mem_filter.mp hβ).2

  set sin : Multiset A := Rin.attach.map fun r => (⟨r.1, hin r.1 r.2⟩ : A) with hsin
  set Pint : Polynomial A := (sin.map fun t => X - C t).prod with hPintdef
  have hPint_monic : Pint.Monic := monic_multisetProd_X_sub_C sin
  have hPint_map : Pint.map (algebraMap A L) = (Rin.map fun a => X - C a).prod := by
    rw [hPintdef, Polynomial.map_multiset_prod, Multiset.map_map, hsin, Multiset.map_map]
    conv_rhs => rw [← Multiset.attach_map_val' Rin]
    refine congrArg _ (Multiset.map_congr rfl fun r _ => ?_)
    simp [Polynomial.map_sub, ValuationSubring.algebraMap_apply]

  set sout : Multiset A := Rout.attach.map fun r =>
    (⟨r.1⁻¹, (ValuationSubring.inv_mem_maximalIdeal_of_not_mem (hout r.1 r.2)).1⟩ : A)
    with hsout
  have hsout_mem : ∀ t ∈ sout, t ∈ IsLocalRing.maximalIdeal A := by
    intro t ht
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.mp ht
    exact (ValuationSubring.inv_mem_maximalIdeal_of_not_mem (hout r.1 r.2)).2
  set Pout : Polynomial A := (sout.map fun t => 1 - C t * X).prod with hPoutdef
  have hPout_map : Pout.map (algebraMap A L) = (Rout.map fun b => (1 : L[X]) - C b⁻¹ * X).prod := by
    rw [hPoutdef, Polynomial.map_multiset_prod, Multiset.map_map, hsout, Multiset.map_map]
    conv_rhs => rw [← Multiset.attach_map_val' Rout]
    refine congrArg _ (Multiset.map_congr rfl fun r _ => ?_)
    simp [Polynomial.map_sub, Polynomial.map_mul, ValuationSubring.algebraMap_apply]
  have hPout_res : Pout.map (IsLocalRing.residue A) = 1 := by
    rw [hPoutdef, Polynomial.map_multiset_prod, Multiset.map_map]
    refine Multiset.prod_eq_one fun q hq => ?_
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hq
    have : IsLocalRing.residue A t = 0 := (IsLocalRing.residue_eq_zero_iff t).mpr (hsout_mem t ht)
    simp [Polynomial.map_sub, Polynomial.map_mul, this]

  set c' : L := (P.map (algebraMap A L)).leadingCoeff * (Rout.map fun b => -b).prod with hc'
  have hfac : P.map (algebraMap A L) = C c' * (Pint * Pout).map (algebraMap A L) := by
    have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.splits (P.map (algebraMap A L))).natDegree_eq_card_roots.symm
    have hlin : ∀ b ∈ Rout, (X : L[X]) - C b = C (-b) * (1 - C b⁻¹ * X) := by
      intro b hb
      have hb0 : b ≠ 0 := fun h => hout b hb (h ▸ A.zero_mem)
      rw [mul_sub, mul_one, ← mul_assoc, ← C_mul, neg_mul, mul_inv_cancel₀ hb0, C_neg, C_neg,
        C_1]
      ring
    have hRout_prod : (Rout.map fun b => (X : L[X]) - C b).prod
        = C (Rout.map fun b => -b).prod * (Rout.map fun b => (1 : L[X]) - C b⁻¹ * X).prod := by
      rw [Multiset.map_congr rfl hlin, Multiset.prod_map_mul, map_multiset_prod C, Multiset.map_map]
      rfl
    conv_lhs => rw [← hsplit, ← hRdef, hR, Multiset.map_add, Multiset.prod_add, hRout_prod]
    rw [Polynomial.map_mul, hPint_map, hPout_map, hc', C_mul]
    ring

  set d : ℕ := Pint.natDegree with hd
  set u : A := (Pint * Pout).coeff d with hu
  have hu_unit : IsUnit u := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu, ← Polynomial.coeff_map, Polynomial.map_mul,
      hPout_res, mul_one, hd, ← hPint_monic.natDegree_map (IsLocalRing.residue A),
      (hPint_monic.map _).coeff_natDegree]
    exact one_ne_zero

  set c : A := P.coeff d * ↑(hu_unit.unit⁻¹) with hcdef
  have hcu : c * u = P.coeff d := by
    rw [hcdef, mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hc' : algebraMap A L c = c' := by
    have h1 : algebraMap A L (P.coeff d) = c' * algebraMap A L u := by
      rw [← Polynomial.coeff_map, hfac, Polynomial.coeff_C_mul, Polynomial.coeff_map]
    have hu0 : algebraMap A L u ≠ 0 := (map_ne_zero_iff _ hinj).mpr hu_unit.ne_zero
    apply mul_right_cancel₀ hu0
    rw [← map_mul, hcu, h1]
  have hP : P = C c * Pint * Pout := by
    apply Polynomial.map_injective (algebraMap A L) hinj
    rw [mul_assoc, Polynomial.map_mul, Polynomial.map_C, hc', ← hfac]
  refine ⟨c, Pint, Pout, hP, hPint_monic, ?_, ?_, ?_⟩
  ·
    intro i
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← Polynomial.coeff_map, hPout_res,
      Polynomial.coeff_one]
    split_ifs <;> simp
  ·
    intro β hβ
    have heval := (Polynomial.mem_roots'.mp hβ).2
    rw [Polynomial.IsRoot.def, hPout_map, Polynomial.eval_multiset_prod, Multiset.map_map,
      Multiset.prod_eq_zero_iff] at heval
    obtain ⟨b, hb, h0⟩ := Multiset.mem_map.mp heval
    have hb0 : b ≠ 0 := fun h => hout b hb (h ▸ A.zero_mem)
    simp only [Function.comp_apply, eval_sub, eval_one, eval_mul, eval_C, eval_X] at h0
    rw [sub_eq_zero, eq_comm, inv_mul_eq_one₀ hb0] at h0
    exact h0 ▸ hout b hb
  ·
    constructor
    · intro hcm i
      rw [hP, mul_assoc, Polynomial.coeff_C_mul]
      exact Ideal.mul_mem_right _ _ hcm
    · intro hall
      rw [hcdef]
      exact Ideal.mul_mem_right _ _ (hall d)

namespace P1

open WithZero IsDedekindDomain

section General
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← exp_log hx0] at hx ⊢
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl, exp_lt_exp] at hx
    rw [exp_le_exp]
    omega

theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := (isUnit_iff_ne_zero.mpr hc).map _
    have h1 : v.adicValuation (algebraMap K F c) = 1 := by
      rw [← v.coe_algebraMap]
      exact (v.adicValuation_coe_eq_one_iff _).mpr hu
    simp only [Place.ord, h1, log_one, neg_zero]

theorem ord_eq_neg_log_of_valuationSubring_eq (w : Valuation F ℤᵐ⁰)
    (hw : w.valuationSubring = v.toValuationSubring) {π : F} (hπ : w π = exp (-1 : ℤ))
    {f : F} (hf : f ≠ 0) : v.ord f = -log (w f) := by
  have hequiv : w.IsEquiv v.adicValuation :=
    v.isEquiv_adicValuation_of_valuationSubring_eq hw
  have hexp_lt : (exp (-1 : ℤ) : ℤᵐ⁰) < 1 := by
    rw [show (1 : ℤᵐ⁰) = exp 0 from rfl]
    exact exp_lt_exp.mpr (by omega)
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hadic_π₀ : v.adicValuation (π₀ : F) = exp (-1 : ℤ) := v.adicValuation_coe_irreducible hπ₀
  have hwπ₀ : w (π₀ : F) = exp (-1 : ℤ) := by
    refine le_antisymm (le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mpr ?_)) ?_
    · rw [hadic_π₀]
      exact hexp_lt
    · rw [← hπ]
      refine (hequiv π π₀).mpr ?_
      rw [hadic_π₀]
      refine le_exp_neg_one_of_lt_one (hequiv.lt_one_iff_lt_one.mp ?_)
      rw [hπ]
      exact hexp_lt
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ₀
  have hwu : w ((u : v.toValuationSubring) : F) = 1 :=
    hequiv.eq_one_iff_eq_one.mpr ((v.adicValuation_coe_eq_one_iff _).mpr u.isUnit)
  set n := v.ord f with hn
  rw [hu, map_mul, map_zpow₀, hwu, hwπ₀, one_mul, log_zpow, log_exp, smul_eq_mul]
  ring

end General

variable {K : Type*} [Field K]

theorem ord_ofHeightOneSpectrum_of_span (w : HeightOneSpectrum K[X]) {p : K[X]}
    (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) p) = 1 := by
  have hval : w.valuation (RatFunc K) (algebraMap K[X] (RatFunc K) p) = exp (-1 : ℤ) := by
    have h := w.intValuation_singleton hp hw
    rw [← h]
    simpa using w.valuation_of_algebraMap (K := RatFunc K) p
  rw [ord_eq_neg_log_of_valuationSubring_eq (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w)
      (w.valuation (RatFunc K)) rfl hval (RatFunc.algebraMap_ne_zero hp), hval]
  simp [log_exp]

theorem ord_ofHeightOneSpectrum_eq_zero_of_notMem (w : HeightOneSpectrum K[X]) {q : K[X]}
    (hq : q ≠ 0) (hmem : q ∉ w.asIdeal) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap K[X] (RatFunc K) q) = 0 := by
  by_contra h
  exact hmem
    ((Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hq).mp h)

theorem ord_placeOfPoint_X_sub_C (a : K) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) = 1 := by
  rw [placeOfPoint_eq_ofHeightOneSpectrum]
  exact ord_ofHeightOneSpectrum_of_span _ (X_sub_C_ne_zero a)
    (heightOneSpectrumOfIrreducible_asIdeal K (irreducible_X_sub_C a))

end P1

section MsDiv

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]

noncomputable def msDiv (t : Multiset K) : Divisor K (RatFunc K) :=
  (t.map fun a => Finsupp.single (placeOfPoint K a) (1 : ℤ)).sum
    - (Multiset.card t : ℤ) • Finsupp.single (placeInfty K) (1 : ℤ)

variable {K}

theorem msDiv_add (s t : Multiset K) : msDiv K (s + t) = msDiv K s + msDiv K t := by
  simp only [msDiv, Multiset.map_add, Multiset.sum_add, Multiset.card_add, Nat.cast_add, add_smul]
  abel

theorem ord_X_sub_C_eq (w : Place K (RatFunc K)) (a : K) :
    w.ord (algebraMap K[X] (RatFunc K) (X - C a))
      = (Finsupp.single (placeOfPoint K a) (1 : ℤ) - Finsupp.single (placeInfty K) (1 : ℤ)) w := by
  classical
  simp only [Finsupp.sub_apply, Finsupp.single_apply]
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty w with ⟨p, rfl⟩ | rfl
  · have hne_inf : placeInfty K ≠ Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) p :=
      placeInfty_ne_ofHeightOneSpectrum K p
    rw [if_neg hne_inf, sub_zero]
    by_cases hw : placeOfPoint K a = Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) p
    · rw [if_pos hw, ← hw, P1.ord_placeOfPoint_X_sub_C]
    · rw [if_neg hw]
      refine P1.ord_ofHeightOneSpectrum_eq_zero_of_notMem p (X_sub_C_ne_zero a) ?_
      intro hmem
      apply hw
      rw [placeOfPoint_eq_ofHeightOneSpectrum]
      congr 1
      refine IsDedekindDomain.HeightOneSpectrum.ext ?_
      have hmax : (Ideal.span {X - C a} : Ideal K[X]).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)
      exact hmax.eq_of_le p.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
  · rw [ord_placeInfty_algebraMap (X_sub_C_ne_zero a), natDegree_X_sub_C,
      if_neg (placeOfPoint_ne_placeInfty K a), if_pos rfl]
    norm_num

omit [DecidableEq (RatFunc K)] in
theorem prod_X_sub_C_ne_zero (s : Multiset K) :
    (s.map fun a => X - C a).prod ≠ 0 :=
  Multiset.prod_ne_zero (fun h => by
    obtain ⟨b, _, hb⟩ := Multiset.mem_map.mp h
    exact X_sub_C_ne_zero b hb)

theorem ord_prod_X_sub_C_eq (w : Place K (RatFunc K)) (s : Multiset K) :
    w.ord (algebraMap K[X] (RatFunc K) (s.map fun a => X - C a).prod) = msDiv K s w := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [msDiv, Place.ord_one]
  | cons a s ih =>
    have h1 : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)
    have h2 : algebraMap K[X] (RatFunc K) ((s.map fun a => X - C a).prod) ≠ 0 :=
      RatFunc.algebraMap_ne_zero (prod_X_sub_C_ne_zero s)
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, w.ord_mul h1 h2, ih, ord_X_sub_C_eq]
    simp only [msDiv, Finsupp.sub_apply, Finsupp.add_apply, Multiset.map_cons, Multiset.sum_cons,
      Multiset.card_cons, Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring

theorem ord_algebraMap_eq_msDiv_roots {R : K[X]} (hR : R ≠ 0) (hsplit : R.Splits)
    (w : Place K (RatFunc K)) :
    w.ord (algebraMap K[X] (RatFunc K) R) = msDiv K R.roots w := by
  classical
  have hlc : R.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hR
  have hC : algebraMap K[X] (RatFunc K) (C R.leadingCoeff) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (C_ne_zero.mpr hlc)
  have hP : algebraMap K[X] (RatFunc K) ((R.roots.map fun a => X - C a).prod) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (prod_X_sub_C_ne_zero R.roots)
  conv_lhs => rw [hsplit.eq_prod_roots]
  rw [map_mul, w.ord_mul hC hP]
  have hC0 : w.ord (algebraMap K[X] (RatFunc K) (C R.leadingCoeff)) = 0 := by
    rw [show algebraMap K[X] (RatFunc K) (C R.leadingCoeff)
        = algebraMap K (RatFunc K) R.leadingCoeff from by
          rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]]
    exact P1.ord_algebraMap w R.leadingCoeff
  rw [hC0, zero_add, ord_prod_X_sub_C_eq]

omit [DecidableEq (RatFunc K)] in

theorem ord_C_mul_eq {c : K} (hc : c ≠ 0) {R : K[X]} (hR : R ≠ 0) (w : Place K (RatFunc K)) :
    w.ord (algebraMap K[X] (RatFunc K) (C c * R)) = w.ord (algebraMap K[X] (RatFunc K) R) := by
  have hC : algebraMap K[X] (RatFunc K) (C c) ≠ 0 := RatFunc.algebraMap_ne_zero (C_ne_zero.mpr hc)
  rw [map_mul, w.ord_mul hC (RatFunc.algebraMap_ne_zero hR),
    show algebraMap K[X] (RatFunc K) (C c) = algebraMap K (RatFunc K) c from by
      rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq],
    P1.ord_algebraMap, zero_add]

omit [DecidableEq (RatFunc K)] in
theorem ord_div_eq {F : Type*} [Field F] [Algebra K F] (w : Place K F) {f g : F} (hf : f ≠ 0)
    (hg : g ≠ 0) : w.ord (f / g) = w.ord f - w.ord g := by
  rw [div_eq_mul_inv, w.ord_mul hf (inv_ne_zero hg), w.ord_inv, sub_eq_add_neg]

theorem mapDomain_msDiv {k : Type*} [Field k] [DecidableEq (RatFunc k)]
    (g : Place K (RatFunc K) → Place k (RatFunc k)) (t : Multiset K) :
    Finsupp.mapDomain g (msDiv K t)
      = (t.map fun a => Finsupp.single (g (placeOfPoint K a)) (1 : ℤ)).sum
          - (Multiset.card t : ℤ) • Finsupp.single (g (placeInfty K)) (1 : ℤ) := by
  rw [msDiv, ← Finsupp.mapDomain.addMonoidHom_apply, map_sub, map_zsmul, map_multiset_sum,
    Multiset.map_map, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
  congr 2
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

end MsDiv

theorem primitive_push_and_reduce
    {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)] {A : ValuationSubring L}
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] (red : A →+* k)
    (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    (sp : Place L (RatFunc L) → Place k (RatFunc k))
    (hsp_int : ∀ a : A, sp (placeOfPoint L (a : L)) = placeOfPoint k (red a))
    (hsp_out : ∀ a : L, a ∉ A → sp (placeOfPoint L a) = placeInfty k)
    (hsp_infty : sp (placeInfty L) = placeInfty k)
    (P : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A) :
    ∃ t : Multiset A,
      P.map (algebraMap A L) ≠ 0 ∧ P.map red ≠ 0 ∧
      Finsupp.mapDomain sp (msDiv L (P.map (algebraMap A L)).roots) = msDiv k (t.map red) ∧
      ∀ v' : Place k (RatFunc k),
        v'.ord (algebraMap k[X] (RatFunc k) (P.map red)) = msDiv k (t.map red) v' := by
  classical
  have hinj : Function.Injective (algebraMap A L) := fun x y h => Subtype.ext h
  obtain ⟨c, Pint, Pout, hfac, hmonic, hPout1, hPoutR, hciff⟩ :=
    exists_eq_C_mul_monic_mul_of_valuationSubring P
  obtain ⟨i, hi⟩ := hP
  have hc : c ∉ IsLocalRing.maximalIdeal A := fun h => hi (hciff.mp h i)
  have hc0 : c ≠ 0 := fun h => hc (h ▸ Ideal.zero_mem _)
  have hcL : algebraMap A L c ≠ 0 := (map_ne_zero_iff _ hinj).mpr hc0
  have hck : red c ≠ 0 := red_ne_zero_of_not_mem red hc
  have hPout0 : Pout ≠ 0 := by
    intro h
    have h0 := hPout1 0
    rw [h, coeff_zero, if_pos rfl, zero_sub, Ideal.neg_mem_iff] at h0
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h0)
  obtain ⟨t, htmap, htfac⟩ := exists_multiset_map_monic_eq_prod (A := A) hmonic
  have hPintL : Pint.map (algebraMap A L)
      = ((t.map (algebraMap A L)).map fun a => X - C a).prod := by
    rw [htfac, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun a _ => by simp [Polynomial.map_sub]
  have hPintk : Pint.map red = ((t.map red).map fun a => X - C a).prod := by
    rw [htfac, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun a _ => by simp [Polynomial.map_sub]
  have hPoutL0 : Pout.map (algebraMap A L) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hPout0
  have hPintL0 : Pint.map (algebraMap A L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hmonic.ne_zero
  have hPL : P.map (algebraMap A L)
      = C (algebraMap A L c) * Pint.map (algebraMap A L) * Pout.map (algebraMap A L) := by
    rw [hfac, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
  have hPk : P.map red = C (red c) * Pint.map red :=
    map_red_eq_of_factorisation red hred hfac hPout1
  have hPL0 : P.map (algebraMap A L) ≠ 0 := by
    rw [hPL]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.mpr hcL) hPintL0) hPoutL0
  have hPk0 : P.map red ≠ 0 := by
    rw [hPk, hPintk]
    exact mul_ne_zero (C_ne_zero.mpr hck) (prod_X_sub_C_ne_zero _)
  have hroots : (P.map (algebraMap A L)).roots
      = t.map (algebraMap A L) + (Pout.map (algebraMap A L)).roots := by
    rw [hPL, mul_assoc, roots_C_mul _ hcL, roots_mul (mul_ne_zero hPintL0 hPoutL0), hPintL,
      roots_multiset_prod_X_sub_C]
  refine ⟨t, hPL0, hPk0, ?_, ?_⟩
  · rw [hroots, msDiv_add, Finsupp.mapDomain_add, mapDomain_msDiv, mapDomain_msDiv, hsp_infty,
      Multiset.map_map, Multiset.card_map]
    have hout : ((Pout.map (algebraMap A L)).roots.map
          fun a => Finsupp.single (sp (placeOfPoint L a)) (1 : ℤ)).sum
        = (Multiset.card (Pout.map (algebraMap A L)).roots : ℤ)
            • Finsupp.single (placeInfty k) (1 : ℤ) := by
      have hrep : ((Pout.map (algebraMap A L)).roots.map
            fun a => Finsupp.single (sp (placeOfPoint L a)) (1 : ℤ))
          = Multiset.replicate (Multiset.card (Pout.map (algebraMap A L)).roots)
              (Finsupp.single (placeInfty k) (1 : ℤ)) := by
        rw [Multiset.eq_replicate]
        refine ⟨Multiset.card_map _ _, fun b hb => ?_⟩
        obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hb
        rw [hsp_out β (hPoutR β hβ)]
      rw [hrep, Multiset.sum_replicate, natCast_zsmul]
    have hin : t.map ((fun a => Finsupp.single (sp (placeOfPoint L a)) (1 : ℤ)) ∘ (algebraMap A L))
        = t.map ((fun a => Finsupp.single (placeOfPoint k a) (1 : ℤ)) ∘ red) := by
      refine Multiset.map_congr rfl fun a _ => ?_
      have h : sp (placeOfPoint L ((algebraMap A L) a)) = placeOfPoint k (red a) := hsp_int a
      simp only [Function.comp_apply, h]
    rw [hout, sub_self, add_zero, hin, msDiv, Multiset.map_map, Multiset.card_map]
  · intro v'
    rw [hPk, hPintk, ord_C_mul_eq hck (prod_X_sub_C_ne_zero _), ord_prod_X_sub_C_eq]

end Ws14Port

open Ws14Port in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [DecidableEq (RatFunc L)] {A : ValuationSubring L}
    {k : Type*} [Field k] [DecidableEq (RatFunc k)] (red : A →+* k)
    (hred : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → red a = 0)
    (sp : Place L (RatFunc L) → Place k (RatFunc k))
    (hsp_int : ∀ a : A, sp (placeOfPoint L (a : L)) = placeOfPoint k (red a))
    (hsp_out : ∀ a : L, a ∉ A → sp (placeOfPoint L a) = placeInfty k)
    (hsp_infty : sp (placeInfty L) = placeInfty k)
    (P Q : Polynomial A) (hP : ∃ i, P.coeff i ∉ IsLocalRing.maximalIdeal A)
    (hQ : ∃ i, Q.coeff i ∉ IsLocalRing.maximalIdeal A)
    (D : Divisor L (RatFunc L))
    (hD : ∀ w, D w = w.ord (algebraMap (Polynomial L) (RatFunc L) (P.map (algebraMap A L))
                              / algebraMap (Polynomial L) (RatFunc L) (Q.map (algebraMap A L)))) :
    ∀ v' : Place k (RatFunc k),
      Finsupp.mapDomain sp D v'
        = v'.ord (algebraMap (Polynomial k) (RatFunc k) (P.map red)
                  / algebraMap (Polynomial k) (RatFunc k) (Q.map red)) := by
  classical
  obtain ⟨tP, hPL0, hPk0, hPpush, hPord⟩ :=
    primitive_push_and_reduce red hred sp hsp_int hsp_out hsp_infty P hP
  obtain ⟨tQ, hQL0, hQk0, hQpush, hQord⟩ :=
    primitive_push_and_reduce red hred sp hsp_int hsp_out hsp_infty Q hQ
  have hDeq : D = msDiv L (P.map (algebraMap A L)).roots - msDiv L (Q.map (algebraMap A L)).roots := by
    ext w
    rw [hD w, Finsupp.sub_apply,
      ord_div_eq w (RatFunc.algebraMap_ne_zero hPL0) (RatFunc.algebraMap_ne_zero hQL0),
      ord_algebraMap_eq_msDiv_roots hPL0 (IsAlgClosed.splits _),
      ord_algebraMap_eq_msDiv_roots hQL0 (IsAlgClosed.splits _)]
  intro v'
  rw [hDeq, ← Finsupp.mapDomain.addMonoidHom_apply, map_sub, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain.addMonoidHom_apply, hPpush, hQpush, Finsupp.sub_apply,
    ord_div_eq v' (RatFunc.algebraMap_ne_zero hPk0) (RatFunc.algebraMap_ne_zero hQk0), hPord, hQord]

end S_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_mapDomain_eq_ord_div_map_of_primitive (solution)
