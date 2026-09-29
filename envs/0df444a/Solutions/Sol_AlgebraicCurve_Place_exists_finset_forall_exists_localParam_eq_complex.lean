-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/36febd52-0c94-546e-8793-9c0df16fe0ef

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.AlgebraicCurve Filter Set Metric Topology Polynomial"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.ord Place.ord_zero Place.ord_inv Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place.evalAt Place.evalAt_one"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg heightOneSpectrum adicValuation adicValuation_ne_zero adicValuation_coe adicValuation_coe_eq_one_iff ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow exists_unit_mul_zpow ne_top' algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one"
namespace FiniteCover
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

section Prelim

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adicValuation_le_one_of_mem (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_eq_exp_neg_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  unfold Place.ord
  rw [neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  have h := adicValuation_le_one_of_mem v hf
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

theorem not_mem_iff_ord_neg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∉ v.toValuationSubring ↔ v.ord f < 0 := by
  constructor
  · intro h
    by_contra hle
    exact h (mem_of_ord_nonneg v hf (not_lt.mp hle))
  · intro h hmem
    have := ord_nonneg_of_mem v hmem
    omega

theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring)
    (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f := by
  have hle : v.adicValuation f ≤ 1 := adicValuation_le_one_of_mem v hf
  have hne : v.adicValuation f ≠ 1 := by
    intro h1
    have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
      (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mp h1
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hmax) hu
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne hle hne
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

theorem residue_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : 0 < v.ord f) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
  intro hu
  have h1 : v.adicValuation f = 1 := (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mpr hu
  by_cases hf0 : f = 0
  · subst hf0; simp at h
  rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero] at h1
  have := WithZero.exp_injective h1
  omega

theorem isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem evalAt_algebraMap (v : Place K F) (c : K) : v.evalAt (algebraMap K F c) = c := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' c)]
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]
  exact v.residueInv_algebraMap c

theorem residue_algebraMap (v : Place K F) (c : K) :
    IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F c, v.algebraMap_mem' c⟩
      = algebraMap K v.ResidueField c := by
  have : (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring c := Subtype.ext (v.coe_algebraMap c).symm
  rw [this]; rfl

theorem evalAt_sub_algebraMap (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (c : K) :
    v.evalAt (f - algebraMap K F c) = v.evalAt f - c := by
  have hc : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hfc : f - algebraMap K F c ∈ v.toValuationSubring := sub_mem hf hc
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv hfc, map_sub, v.algebraMap_evalAt hv hf, ← residue_algebraMap v c,
    ← map_sub]
  rfl

theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (hf0 : f ≠ 0) (h : 0 < v.ord f) :
    v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v hf0 h.le
  rw [v.evalAt_of_mem hf, residue_eq_zero_of_ord_pos v hf h, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  refine ord_pos_of_mem_maximalIdeal v hf0 hf ?_
  rw [← IsLocalRing.residue_eq_zero_iff, ← v.algebraMap_evalAt hv hf, h0, map_zero]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap v (0 : K)

theorem evalAt_eq_of_ord_sub_algebraMap_pos (w : Place K F) (hw : w.IsRational) (t : F) (c : K)
    (h : 0 < w.ord (t - algebraMap K F c)) : w.evalAt t = c := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne h.le
  have ht : t ∈ w.toValuationSubring := by
    simpa using add_mem hmem (w.algebraMap_mem' c)
  have h0 : w.evalAt (t - algebraMap K F c) = 0 := evalAt_eq_zero_of_ord_pos w hne h
  rw [evalAt_sub_algebraMap w hw ht c] at h0
  exact sub_eq_zero.mp h0

theorem mem_of_ord_sub_algebraMap_pos (w : Place K F) (t : F) (c : K)
    (h : 0 < w.ord (t - algebraMap K F c)) : t ∈ w.toValuationSubring := by
  have hne : t - algebraMap K F c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : t - algebraMap K F c ∈ w.toValuationSubring := mem_of_ord_nonneg w hne h.le
  simpa using add_mem hmem (w.algebraMap_mem' c)

theorem ord_sub_evalAt_pos (w : Place K F) (hw : w.IsRational) {f : F}
    (hf : f ∈ w.toValuationSubring) (hne : f - algebraMap K F (w.evalAt f) ≠ 0) :
    0 < w.ord (f - algebraMap K F (w.evalAt f)) := by
  refine ord_pos_of_evalAt_eq_zero w hw hne (sub_mem hf (w.algebraMap_mem' _)) ?_
  rw [evalAt_sub_algebraMap w hw hf, sub_self]

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  by_cases hc : c = 0
  · simp [hc]
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := (IsUnit.mk0 c hc).map _
  have := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec, Place.coe_algebraMap] at this

theorem sub_algebraMap_mem_iff (v : Place K F) (f : F) (a : K) :
    f - algebraMap K F a ∈ v.toValuationSubring ↔ f ∈ v.toValuationSubring := by
  constructor
  · intro h; simpa using add_mem h (v.algebraMap_mem' a)
  · intro h; exact sub_mem h (v.algebraMap_mem' a)

theorem ord_sub_algebraMap_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring)
    (a : K) : v.ord (f - algebraMap K F a) = v.ord f := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  have hfa : f - algebraMap K F a ∉ v.toValuationSubring := by
    rwa [sub_algebraMap_mem_iff]
  have hfa0 : f - algebraMap K F a ≠ 0 := fun h => hfa (h ▸ zero_mem _)
  have hlt : v.adicValuation (algebraMap K F a) < v.adicValuation f := by
    have h1 : v.adicValuation (algebraMap K F a) ≤ 1 :=
      adicValuation_le_one_of_mem v (v.algebraMap_mem' a)
    have h2 : 1 < v.adicValuation f := by
      have hneg := (not_mem_iff_ord_neg v hf0).mp hf
      rw [adicValuation_eq_exp_neg_ord v hf0, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    exact h1.trans_lt h2
  have hval : v.adicValuation (f - algebraMap K F a) = v.adicValuation f :=
    Valuation.map_sub_eq_of_lt_left _ hlt
  unfold Place.ord
  rw [hval]

theorem exists_mem_and_not_mem {v w : Place K F} (hne : v ≠ w) :
    ∃ s : F, s ∈ v.toValuationSubring ∧ s ∉ w.toValuationSubring := by
  by_contra hcon
  push Not at hcon

  apply hne
  apply Place.ext
  refine le_antisymm (fun s hs => hcon s hs) fun x hx => ?_
  by_contra hxv
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ zero_mem _)

  obtain ⟨y, hyw⟩ : ∃ y : F, y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact w.ne_top' (eq_top_iff.mpr fun y _ => hall y)
  have hyv : y ∉ v.toValuationSubring := fun h => hyw (hcon y h)
  have hy0 : y ≠ 0 := fun h => hyw (h ▸ zero_mem _)

  have hxneg : v.ord x < 0 := (not_mem_iff_ord_neg v hx0).mp hxv
  have hyneg : v.ord y < 0 := (not_mem_iff_ord_neg v hy0).mp hyv

  set j : ℤ := -v.ord x with hj
  set k : ℤ := -v.ord y with hk
  set u : F := y ^ j * x⁻¹ ^ k with hu
  have hu0 : u ≠ 0 := mul_ne_zero (zpow_ne_zero _ hy0) (zpow_ne_zero _ (inv_ne_zero hx0))
  have hordu : v.ord u = 0 := by
    rw [hu, v.ord_mul (zpow_ne_zero _ hy0) (zpow_ne_zero _ (inv_ne_zero hx0)), v.ord_zpow,
      v.ord_zpow, v.ord_inv, hj, hk]
    ring

  have huinv : u⁻¹ ∈ w.toValuationSubring :=
    hcon _ (mem_of_ord_nonneg v (inv_ne_zero hu0) (by rw [v.ord_inv, hordu]; simp))
  have huw : u ∈ w.toValuationSubring := by

    have hyj : y ^ j = u * x ^ k := by
      rw [hu, mul_assoc, ← mul_zpow, inv_mul_cancel₀ hx0, one_zpow, mul_one]

    exact hcon _ (mem_of_ord_nonneg v hu0 hordu.ge)
  have hyj_mem : y ^ j ∈ w.toValuationSubring := by
    have hyj : y ^ j = u * x ^ k := by
      rw [hu, mul_assoc, ← mul_zpow, inv_mul_cancel₀ hx0, one_zpow, mul_one]
    rw [hyj]
    have hk0 : 0 ≤ k := by omega
    have hxk : x ^ k ∈ w.toValuationSubring := by
      rw [show k = ((k.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hk0).symm, zpow_natCast]
      exact pow_mem hx _
    exact mul_mem huw hxk

  have h1 : 0 ≤ w.ord (y ^ j) := ord_nonneg_of_mem w hyj_mem
  rw [w.ord_zpow] at h1
  have hj0 : 0 < j := by omega
  have h2 : 0 ≤ w.ord y := by
    by_contra hlt
    push Not at hlt
    have : j * w.ord y < 0 := mul_neg_of_pos_of_neg hj0 hlt
    omega
  exact hyw (mem_of_ord_nonneg w hy0 h2)

theorem sum_support_eq_zero [IsAlgClosed K] [IsCurveOver K F] (D : Divisor K F)
    (hD : Divisor.degree D = 0) : ∑ w ∈ D.support, D w = 0 := by
  have h : Divisor.degree D = ∑ w ∈ D.support, D w * (w.deg : ℤ) := by
    simp only [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum,
      AddMonoidHom.coe_mulRight]
  simp only [IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] at h
  rw [← h, hD]

end Prelim

section Elementary

theorem exists_pos_forall_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ p i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, hδs⟩ := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    refine ⟨min δ (p a), lt_min hδ (hp a (Finset.mem_insert_self a s)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδs i hi)

end Elementary

section Analytic

theorem exists_analyticAt_pow_eq {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (h0 : h 0 ≠ 0) {e : ℕ}
    (he : 0 < e) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k 0 ∧ k 0 ≠ 0 ∧ ∀ᶠ u in 𝓝 0, k u ^ e = h u := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (h 0) he
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow he.ne'] at hβ
    exact h0 hβ.symm
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  refine ⟨fun u => β * Complex.exp (Complex.log (h u / h 0) / e), ?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun u => h u / h 0) 0 := hh.div analyticAt_const h0
    have hslit : (fun u => h u / h 0) 0 ∈ Complex.slitPlane := by
      simp only [div_self h0]
      exact Complex.one_mem_slitPlane
    have h2 : AnalyticAt ℂ (fun u => Complex.log (h u / h 0) / e) 0 :=
      (h1.clog hslit).div analyticAt_const he0
    exact analyticAt_const.mul h2.cexp'
  · simp only [div_self h0, Complex.log_one, zero_div, Complex.exp_zero, mul_one]
    exact hβ0
  · filter_upwards [hh.continuousAt.eventually_ne h0] with u hu
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ he0,
      Complex.exp_log (div_ne_zero hu h0), hβ, mul_div_cancel₀ _ h0]

theorem exists_finset_preimages_of_meromorphicOrderAt_eq {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 0)
    {e : ℕ} (he : 0 < e) (hGe : meromorphicOrderAt G 0 = (e : ℤ)) {r : ℝ} (hr : 0 < r) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : ℂ, a ≠ 0 → ‖a‖ < η →
      ∃ U : Finset ℂ, e ≤ U.card ∧ ∀ u ∈ U, ‖u‖ < r ∧ G u = a := by
  classical

  obtain ⟨h, hh, hh0, hGh⟩ := (meromorphicOrderAt_eq_int_iff hG.meromorphicAt).mp hGe
  simp only [sub_zero, zpow_natCast, smul_eq_mul] at hGh

  obtain ⟨k, hk, hk0, hkh⟩ := exists_analyticAt_pow_eq hh hh0 he

  set ψ : ℂ → ℂ := fun u => u * k u with hψ_def
  have hψan : AnalyticAt ℂ ψ 0 := analyticAt_id.mul hk
  have hψ0 : ψ 0 = 0 := by simp [hψ_def]
  have hderiv : HasDerivAt ψ (k 0) 0 := by
    have := (hasDerivAt_id (0 : ℂ)).mul hk.differentiableAt.hasDerivAt
    simp at this
    exact this
  have hstrict : HasStrictDerivAt ψ (k 0) 0 := by
    have h1 := hψan.hasStrictDerivAt
    rwa [hderiv.deriv] at h1
  have hGψ : ∀ᶠ u in 𝓝[≠] (0 : ℂ), G u = ψ u ^ e := by
    filter_upwards [hGh, hkh.filter_mono nhdsWithin_le_nhds] with u hu hku
    rw [hu, hψ_def, mul_pow, hku]

  have hinj : ∀ᶠ u in 𝓝 (0 : ℂ),
      hstrict.localInverse ψ (k 0) 0 hk0 (ψ u) = u := hstrict.eventually_left_inverse hk0

  obtain ⟨r₁, hr₁, hr₁sub⟩ :=
    Metric.mem_nhds_iff.mp (hinj.and (eventually_nhdsWithin_iff.mp hGψ))
  set r' := min r r₁ with hr'_def
  have hr' : 0 < r' := lt_min hr hr₁
  have hball : ∀ u : ℂ, ‖u‖ < r' →
      hstrict.localInverse ψ (k 0) 0 hk0 (ψ u) = u ∧ (u ≠ 0 → G u = ψ u ^ e) := by
    intro u hu
    have hu' : u ∈ ball (0 : ℂ) r₁ := by
      rw [mem_ball, dist_zero_right]; exact hu.trans_le (min_le_right _ _)
    exact hr₁sub hu'

  have himage : ψ '' ball (0 : ℂ) r' ∈ 𝓝 (0 : ℂ) := by
    have h1 : map ψ (𝓝 0) = 𝓝 (ψ 0) := hstrict.map_nhds_eq hk0
    rw [hψ0] at h1
    rw [← h1]
    exact image_mem_map (ball_mem_nhds 0 hr')
  obtain ⟨s, hs, hssub⟩ := Metric.mem_nhds_iff.mp himage

  refine ⟨s ^ e, pow_pos hs e, fun a ha0 has => ?_⟩

  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / e)) e :=
    Complex.isPrimitiveRoot_exp e he.ne'
  set B : Finset ℂ := (nthRoots e a).toFinset with hB_def
  have hBcard : B.card = e := by
    rw [hB_def, Multiset.toFinset_card_of_nodup (hζ.nthRoots_nodup ha0), hζ.card_nthRoots,
      if_pos (IsAlgClosed.exists_pow_nat_eq a he)]
  have hBmem : ∀ b ∈ B, b ^ e = a := by
    intro b hb
    rw [hB_def, Multiset.mem_toFinset, mem_nthRoots he] at hb
    exact hb
  have hBsmall : ∀ b ∈ B, b ∈ ball (0 : ℂ) s := by
    intro b hb
    rw [mem_ball, dist_zero_right]
    have h1 : ‖b‖ ^ e < s ^ e := by rw [← norm_pow, hBmem b hb]; exact has
    exact lt_of_pow_lt_pow_left₀ e hs.le h1

  have hpre : ∀ b ∈ B, ∃ u : ℂ, ‖u‖ < r' ∧ ψ u = b := by
    intro b hb
    obtain ⟨u, hu, hub⟩ := hssub (hBsmall b hb)
    rw [mem_ball, dist_zero_right] at hu
    exact ⟨u, hu, hub⟩
  choose! σ hσ hψσ using hpre
  refine ⟨B.image σ, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hBcard]
    intro b hb b' hb' hbb'
    have := congrArg ψ hbb'
    rwa [hψσ b hb, hψσ b' hb'] at this
  · intro u hu
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨(hσ b hb).trans_le (min_le_left _ _), ?_⟩
    have hσ0 : σ b ≠ 0 := by
      intro h0
      have : b = 0 := by rw [← hψσ b hb, h0, hψ0]
      rw [this] at hb
      have := hBmem 0 hb
      rw [zero_pow he.ne'] at this
      exact ha0 this.symm
    rw [(hball (σ b) (hσ b hb)).2 hσ0, hψσ b hb, hBmem b hb]

end Analytic

section Family

variable (F : Type*) [Field F] [Algebra ℂ F]

structure Fam where

  ρ : Place ℂ F → ℝ

  γ : Place ℂ F → ℂ → Place ℂ F

  t : Place ℂ F → F
  hρ : ∀ v, 0 < ρ v
  h₀ : ∀ v, γ v 0 = v
  ht : ∀ v, ∀ z ∈ Metric.ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1
  hγ : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) (ρ v),
    MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
    meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
    (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)

variable {F} [IsCurveOver ℂ F] (P : Fam F)

namespace Fam

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isCurveOver w

omit [IsCurveOver ℂ F] in
theorem zero_mem_ball (v : Place ℂ F) : (0 : ℂ) ∈ ball (0 : ℂ) (P.ρ v) :=
  mem_ball_self (P.hρ v)

theorem evalAt_γ_t (v : Place ℂ F) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (P.ρ v)) :
    (P.γ v z).evalAt (P.t v) = z :=
  evalAt_eq_of_ord_sub_algebraMap_pos _ (isRational _) _ _ (by rw [P.ht v z hz]; exact one_pos)

theorem γ_injOn (v : Place ℂ F) : InjOn (P.γ v) (ball (0 : ℂ) (P.ρ v)) := by
  intro z hz z' hz' h
  rw [← P.evalAt_γ_t v hz, ← P.evalAt_γ_t v hz', h]

omit [IsCurveOver ℂ F] in

theorem analyticAt_reading (v : Place ℂ F) {g : F} (hg : g ∈ v.toValuationSubring) :
    AnalyticAt ℂ (fun u : ℂ => (P.γ v u).evalAt g) 0 := by
  by_cases hg0 : g = 0
  · subst hg0
    simp only [evalAt_zero]
    exact analyticAt_const
  have h := (P.hγ v g hg0 0 (P.zero_mem_ball v)).2.2
  rw [P.h₀] at h
  exact h (ord_nonneg_of_mem v hg)

omit [IsCurveOver ℂ F] in

theorem meromorphicOrderAt_reading (v : Place ℂ F) {g : F} (hg0 : g ≠ 0) :
    meromorphicOrderAt (fun u : ℂ => (P.γ v u).evalAt g) 0 = (v.ord g : WithTop ℤ) := by
  have h := (P.hγ v g hg0 0 (P.zero_mem_ball v)).2.1
  rwa [P.h₀] at h

omit [IsCurveOver ℂ F] in

theorem eventually_mem (v : Place ℂ F) {g : F} (hg : g ∈ v.toValuationSubring) :
    ∀ᶠ u in 𝓝 (0 : ℂ), g ∈ (P.γ v u).toValuationSubring := by
  by_cases hg0 : g = 0
  · exact Eventually.of_forall fun u => by rw [hg0]; exact zero_mem _
  filter_upwards [(P.analyticAt_reading v hg).eventually_analyticAt,
    isOpen_ball.mem_nhds (P.zero_mem_ball v)] with u hu huU
  have h := (P.hγ v g hg0 u huU).2.1
  have hnn : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun u : ℂ => (P.γ v u).evalAt g) u :=
    hu.meromorphicOrderAt_nonneg
  rw [h] at hnn
  exact mem_of_ord_nonneg _ hg0 (by exact_mod_cast hnn)

omit [IsCurveOver ℂ F] in

theorem exists_radius_mem (v : Place ℂ F) {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → g ∈ (P.γ v u).toValuationSubring := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp (P.eventually_mem v hg)
  exact ⟨δ, hδ, fun u hu => h u (by rwa [mem_ball, dist_zero_right])⟩

theorem separation {v w : Place ℂ F} (hne : v ≠ w) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ δ' : ℝ, 0 < δ' ∧
      ∀ u u' : ℂ, ‖u‖ < δ → ‖u'‖ < δ' → P.γ v u ≠ P.γ w u' := by
  obtain ⟨s, hsv, hsw⟩ := exists_mem_and_not_mem hne
  have hs0 : s ≠ 0 := fun h => hsw (h ▸ zero_mem _)
  have hsiw : s⁻¹ ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem s).resolve_left hsw
  have hordw : 0 < w.ord s⁻¹ := by
    rw [Place.ord_inv]
    have := (not_mem_iff_ord_neg w hs0).mp hsw
    omega

  have hR : AnalyticAt ℂ (fun u : ℂ => (P.γ v u).evalAt s) 0 := P.analyticAt_reading v hsv
  set M : ℝ := ‖(P.γ v 0).evalAt s‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  have h1 : ∀ᶠ u in 𝓝 (0 : ℂ), ‖(P.γ v u).evalAt s‖ < M := by
    have hc : ContinuousAt (fun u : ℂ => ‖(P.γ v u).evalAt s‖) 0 := hR.continuousAt.norm
    exact hc.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), s ∈ (P.γ v u).toValuationSubring := P.eventually_mem v hsv

  have hR' : AnalyticAt ℂ (fun u : ℂ => (P.γ w u).evalAt s⁻¹) 0 := P.analyticAt_reading w hsiw
  have hR'0 : (P.γ w 0).evalAt s⁻¹ = 0 := by
    rw [P.h₀]; exact evalAt_eq_zero_of_ord_pos w (inv_ne_zero hs0) hordw
  have h3 : ∀ᶠ u in 𝓝 (0 : ℂ), ‖(P.γ w u).evalAt s⁻¹‖ < M⁻¹ := by
    have hc : ContinuousAt (fun u : ℂ => ‖(P.γ w u).evalAt s⁻¹‖) 0 := hR'.continuousAt.norm
    have hlt : ‖(P.γ w 0).evalAt s⁻¹‖ < M⁻¹ := by
      rw [hR'0, norm_zero]; exact inv_pos.mpr hMpos
    exact hc.eventually (gt_mem_nhds hlt)
  have h4 : ∀ᶠ u in 𝓝 (0 : ℂ), s⁻¹ ∈ (P.γ w u).toValuationSubring := P.eventually_mem w hsiw
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  obtain ⟨δ', hδ', hδb'⟩ := Metric.eventually_nhds_iff_ball.mp (h3.and h4)
  refine ⟨δ, hδ, δ', hδ', fun u u' hu hu' heq => ?_⟩
  obtain ⟨hlt, hmem⟩ := hδb u (by rwa [mem_ball, dist_zero_right])
  obtain ⟨hlt', hmem'⟩ := hδb' u' (by rwa [mem_ball, dist_zero_right])
  rw [← heq] at hlt' hmem'
  have hprod : (P.γ v u).evalAt s * (P.γ v u).evalAt s⁻¹ = 1 := by
    rw [← evalAt_mul _ (isRational _) hmem hmem', mul_inv_cancel₀ hs0, Place.evalAt_one]
  have hlt1 : ‖(P.γ v u).evalAt s * (P.γ v u).evalAt s⁻¹‖ < 1 := by
    rw [norm_mul]
    calc ‖(P.γ v u).evalAt s‖ * ‖(P.γ v u).evalAt s⁻¹‖
        ≤ M * ‖(P.γ v u).evalAt s⁻¹‖ := by gcongr
      _ < M * M⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hMpos.ne'
  rw [hprod, norm_one] at hlt1
  exact lt_irrefl _ hlt1

theorem fibre {g : F} (hg : ∀ c : ℂ, g ≠ algebraMap ℂ F c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : Finset (Place ℂ F), ∃ δ : Place ℂ F → ℝ,
      (∀ w ∈ T, 0 < δ w ∧ δ w < P.ρ w) ∧ (∀ w ∈ T, 0 < w.ord g) ∧
      ∀ a : ℂ, ‖a‖ < ε → ∀ w' : Place ℂ F, 0 < w'.ord (g - algebraMap ℂ F a) →
        ∃ w ∈ T, ∃ u : ℂ, ‖u‖ < δ w ∧ P.γ w u = w' := by
  classical
  have hg0 : g ≠ 0 := by simpa using hg 0
  have hga : ∀ a : ℂ, g - algebraMap ℂ F a ≠ 0 := fun a h => hg a (sub_eq_zero.mp h)

  have hdiv : ∀ a : ℂ, ∃ D : Divisor ℂ F,
      (∀ w, D w = w.ord (g - algebraMap ℂ F a)) ∧ Divisor.degree D = 0 :=
    fun a => HasPrincipalDivisors.exists_divisor _ (hga a)
  choose D hD hdeg using hdiv

  set Z : ℂ → Finset (Place ℂ F) := fun a => (D a).support.filter (fun w => 0 < D a w) with hZ
  have memZ : ∀ a w, w ∈ Z a ↔ 0 < w.ord (g - algebraMap ℂ F a) := by
    intro a w
    simp only [hZ, Finset.mem_filter, Finsupp.mem_support_iff, hD]
    exact ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩
  have posZ : ∀ a, ∀ w ∈ Z a, 0 < D a w := fun a w hw => (Finset.mem_filter.mp hw).2

  set Pl : ℂ → Finset (Place ℂ F) := fun a => (D a).support.filter (fun w => D a w < 0) with hPl
  have memPl : ∀ a w, w ∈ Pl a ↔ g ∉ w.toValuationSubring := by
    intro a w
    simp only [hPl, Finset.mem_filter, Finsupp.mem_support_iff, hD]
    rw [← sub_algebraMap_mem_iff w g a, not_mem_iff_ord_neg w (hga a)]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  have sumPl : ∀ a, ∑ w ∈ Pl a, D a w = ∑ w ∈ Pl 0, D 0 w := by
    intro a
    have hset : Pl a = Pl 0 := by
      ext w; rw [memPl, memPl]
    rw [hset]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hgw : g ∉ w.toValuationSubring := (memPl 0 w).mp hw
    rw [hD, hD, ord_sub_algebraMap_of_not_mem w hgw, ord_sub_algebraMap_of_not_mem w hgw]

  have split : ∀ a, ∑ w ∈ Z a, D a w + ∑ w ∈ Pl a, D a w = 0 := by
    intro a
    rw [← sum_support_eq_zero (D a) (hdeg a), hZ, hPl]
    rw [← Finset.sum_filter_add_sum_filter_not (D a).support (fun w => 0 < D a w)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext w
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, not_lt]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_of_lt h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_ne h2 h1⟩
  have sumZ : ∀ a, ∑ w ∈ Z a, D a w = ∑ w ∈ Z 0, D 0 w := by
    intro a
    have h1 := split a
    have h2 := split 0
    rw [sumPl a] at h1
    linarith

  set T : Finset (Place ℂ F) := Z 0 with hT_def
  have hT : ∀ w ∈ T, 0 < w.ord g := by
    intro w hw
    have := (memZ 0 w).mp hw
    simpa using this
  have hTmem : ∀ w ∈ T, g ∈ w.toValuationSubring := fun w hw =>
    mem_of_ord_nonneg w hg0 (hT w hw).le

  have hsep : ∀ w w' : Place ℂ F, w ≠ w' → ∃ δ : ℝ, 0 < δ ∧ ∃ δ' : ℝ, 0 < δ' ∧
      ∀ u u' : ℂ, ‖u‖ < δ → ‖u'‖ < δ' → P.γ w u ≠ P.γ w' u' := fun w w' h => P.separation h
  choose! Δ hΔ Δ' hΔ' hsepΔ using hsep
  have hδ₁ : ∀ w : Place ℂ F, ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ w' ∈ T, w' ≠ w → δ₁ ≤ Δ w w' ∧ δ₁ ≤ Δ' w' w := by
    intro w
    obtain ⟨δ₁, h1, h2⟩ := exists_pos_forall_le (T.erase w) (fun w' => min (Δ w w') (Δ' w' w))
      (fun w' hw' => lt_min (hΔ w w' (Finset.ne_of_mem_erase hw').symm)
        (hΔ' w' w (Finset.ne_of_mem_erase hw')))
    refine ⟨δ₁, h1, fun w' hw' hne => ?_⟩
    have := h2 w' (Finset.mem_erase.mpr ⟨hne, hw'⟩)
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩
  choose δ₁ hδ₁pos hδ₁le using hδ₁

  have hδ₂ : ∀ w : Place ℂ F, ∃ δ₂ : ℝ, 0 < δ₂ ∧
      (g ∈ w.toValuationSubring → ∀ u : ℂ, ‖u‖ < δ₂ → g ∈ (P.γ w u).toValuationSubring) := by
    intro w
    by_cases hw : g ∈ w.toValuationSubring
    · obtain ⟨δ₂, h1, h2⟩ := P.exists_radius_mem w hw
      exact ⟨δ₂, h1, fun _ => h2⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose δ₂ hδ₂pos hδ₂mem using hδ₂

  set δ : Place ℂ F → ℝ := fun w => min (min (δ₁ w) (δ₂ w)) (P.ρ w / 2) with hδ_def
  have hδpos : ∀ w, 0 < δ w := fun w =>
    lt_min (lt_min (hδ₁pos w) (hδ₂pos w)) (half_pos (P.hρ w))
  have hδρ : ∀ w, δ w < P.ρ w := fun w =>
    (min_le_right _ _).trans_lt (half_lt_self (P.hρ w))
  have hδle₁ : ∀ w, δ w ≤ δ₁ w := fun w => (min_le_left _ _).trans (min_le_left _ _)
  have hδle₂ : ∀ w, δ w ≤ δ₂ w := fun w => (min_le_left _ _).trans (min_le_right _ _)

  have hη : ∀ w : Place ℂ F, ∃ η : ℝ, 0 < η ∧ (w ∈ T → ∀ a : ℂ, a ≠ 0 → ‖a‖ < η →
      ∃ U : Finset ℂ, (D 0 w).toNat ≤ U.card ∧
        ∀ u ∈ U, ‖u‖ < δ w ∧ (P.γ w u).evalAt g = a) := by
    intro w
    by_cases hw : w ∈ T
    · have hpos : 0 < D 0 w := posZ 0 w hw
      have he : 0 < (D 0 w).toNat := by omega
      have han : AnalyticAt ℂ (fun u : ℂ => (P.γ w u).evalAt g) 0 :=
        P.analyticAt_reading w (hTmem w hw)
      have horder : meromorphicOrderAt (fun u : ℂ => (P.γ w u).evalAt g) 0
          = (((D 0 w).toNat : ℕ) : ℤ) := by
        rw [P.meromorphicOrderAt_reading w hg0, Int.toNat_of_nonneg hpos.le, hD 0 w, map_zero,
          sub_zero]
      obtain ⟨η, hη, H⟩ :=
        exists_finset_preimages_of_meromorphicOrderAt_eq han he horder (hδpos w)
      exact ⟨η, hη, fun _ => H⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose η hηpos hηU using hη
  obtain ⟨ε, hε, hεle⟩ := exists_pos_forall_le T η (fun w _ => hηpos w)
  refine ⟨ε, hε, T, δ, fun w _ => ⟨hδpos w, hδρ w⟩, hT, fun a ha w' hw' => ?_⟩

  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨w', (memZ 0 w').mpr hw', 0, by simpa using hδpos w', P.h₀ w'⟩

  have hU : ∀ w ∈ T, ∃ U : Finset ℂ, (D 0 w).toNat ≤ U.card ∧
      ∀ u ∈ U, ‖u‖ < δ w ∧ (P.γ w u).evalAt g = a :=
    fun w hw => hηU w hw a ha0 (ha.trans_le (hεle w hw))
  choose! U hUcard hUmem using hU
  set Q : Finset (Σ _ : Place ℂ F, ℂ) := T.sigma fun w => U w with hQ_def
  set ι : (Σ _ : Place ℂ F, ℂ) → Place ℂ F := fun q => P.γ q.1 q.2 with hι_def

  have hιZ : ∀ q ∈ Q, ι q ∈ Z a := by
    rintro ⟨w, u⟩ hq
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hu1, hu2⟩ := hUmem w hw u hu
    rw [memZ]
    have hgm : g ∈ (P.γ w u).toValuationSubring :=
      hδ₂mem w (hTmem w hw) u (hu1.trans_le (hδle₂ w))
    refine ord_pos_of_evalAt_eq_zero _ (isRational _) (hga a)
      (sub_mem hgm ((P.γ w u).algebraMap_mem' a)) ?_
    rw [evalAt_sub_algebraMap _ (isRational _) hgm, hu2, sub_self]
  have hιZ' : ∀ p ∈ Q.image ι, p ∈ Z a := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hιZ q hq

  have hinj : Set.InjOn ι (Q : Set (Σ _ : Place ℂ F, ℂ)) := by
    rintro ⟨w, u⟩ hq ⟨w', u'⟩ hq' heq
    rw [Finset.mem_coe] at hq hq'
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hw', hu'⟩ := Finset.mem_sigma.mp hq'
    obtain ⟨hu1, -⟩ := hUmem w hw u hu
    obtain ⟨hu1', -⟩ := hUmem w' hw' u' hu'
    change P.γ w u = P.γ w' u' at heq
    by_cases hww : w = w'
    · subst hww
      have huu : u = u' := P.γ_injOn w
        (by rw [mem_ball, dist_zero_right]; exact hu1.trans (hδρ w))
        (by rw [mem_ball, dist_zero_right]; exact hu1'.trans (hδρ w)) heq
      subst huu
      rfl
    · exfalso
      have h1 := (hδ₁le w w' hw' (Ne.symm hww)).1
      have h2 := (hδ₁le w' w hw hww).2
      exact hsepΔ w w' hww u u' (hu1.trans_le ((hδle₁ w).trans h1))
        (hu1'.trans_le ((hδle₁ w').trans h2)) heq

  have hcard : ((Q.image ι).card : ℤ) = ∑ w ∈ T, ((U w).card : ℤ) := by
    rw [Finset.card_image_of_injOn hinj, hQ_def, Finset.card_sigma]
    push_cast
    rfl
  have hn_le : ∑ w ∈ T, D 0 w ≤ ((Q.image ι).card : ℤ) := by
    rw [hcard]
    refine Finset.sum_le_sum fun w hw => ?_
    calc D 0 w = (((D 0 w).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (posZ 0 w hw).le).symm
      _ ≤ ((U w).card : ℤ) := by exact_mod_cast hUcard w hw
  by_contra hnot
  push Not at hnot
  have hw'not : w' ∉ Q.image ι := by
    intro h
    obtain ⟨⟨w, u⟩, hq, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hq
    exact hnot w hw u (hUmem w hw u hu).1 heq
  have hw'Z : w' ∈ Z a := (memZ a w').mpr hw'
  have hsub : Q.image ι ⊆ (Z a).erase w' := fun p hp =>
    Finset.mem_erase.mpr ⟨fun h => hw'not (h ▸ hp), hιZ' p hp⟩
  have h1 : ∑ p ∈ Q.image ι, D a p ≤ ∑ p ∈ (Z a).erase w', D a p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => (posZ a p (Finset.mem_of_mem_erase hp)).le)
  have h2 : ∑ p ∈ (Z a).erase w', D a p < ∑ p ∈ Z a, D a p := by
    rw [← Finset.add_sum_erase _ _ hw'Z]
    linarith [posZ a w' hw'Z]
  have h3 : ((Q.image ι).card : ℤ) ≤ ∑ p ∈ Q.image ι, D a p := by
    have := Finset.card_nsmul_le_sum (Q.image ι) (fun p => D a p) 1
      (fun p hp => Int.add_one_le_of_lt (posZ a p (hιZ' p hp)))
    simpa using this
  have h4 : ∑ p ∈ Z a, D a p = ∑ w ∈ T, D 0 w := sumZ a
  linarith

theorem exists_finset_cover :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < P.ρ v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ P.γ v z = w := by
  classical
  rcases isEmpty_or_nonempty (Place ℂ F) with hE | ⟨⟨v₀⟩⟩
  · exact ⟨∅, fun _ => 0, by simp, fun w => isEmptyElim w⟩

  set f : F := P.t v₀ with hf_def
  have hf0 : f ≠ 0 := by
    intro h
    have h1 := P.ht v₀ 0 (P.zero_mem_ball v₀)
    rw [map_zero, sub_zero, ← hf_def, h, Place.ord_zero] at h1
    exact zero_ne_one h1
  have hf : ∀ c : ℂ, f ≠ algebraMap ℂ F c := by
    intro c hc
    have h1 := P.ht v₀ 0 (P.zero_mem_ball v₀)
    rw [map_zero, sub_zero, ← hf_def, hc, ord_algebraMap] at h1
    exact zero_ne_one h1
  have hfi : ∀ c : ℂ, f⁻¹ ≠ algebraMap ℂ F c := by
    intro c hc
    apply hf c⁻¹
    rw [map_inv₀, ← hc, inv_inv]
  have hfc : ∀ c c' : ℂ, f - algebraMap ℂ F c ≠ algebraMap ℂ F c' := by
    intro c c' h
    apply hf (c' + c)
    rw [map_add, ← h, sub_add_cancel]

  have hfib : ∀ c : ℂ, ∃ ε : ℝ, 0 < ε ∧ ∃ T : Finset (Place ℂ F), ∃ δ : Place ℂ F → ℝ,
      (∀ w ∈ T, 0 < δ w ∧ δ w < P.ρ w) ∧ (∀ w ∈ T, 0 < w.ord (f - algebraMap ℂ F c)) ∧
      ∀ a : ℂ, ‖a‖ < ε → ∀ w' : Place ℂ F,
        0 < w'.ord (f - algebraMap ℂ F c - algebraMap ℂ F a) →
        ∃ w ∈ T, ∃ u : ℂ, ‖u‖ < δ w ∧ P.γ w u = w' := fun c => P.fibre (hfc c)
  choose ε hε T δ hδ hT hcov using hfib
  obtain ⟨εi, hεi, Ti, δi, hδi, hTi, hcovi⟩ := P.fibre hfi

  set R : ℝ := εi⁻¹ with hR_def
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).elim_finite_subcover
    (fun c : ℂ => ball c (ε c)) (fun _ => isOpen_ball)
    (fun c _ => mem_iUnion.mpr ⟨c, mem_ball_self (hε c)⟩)

  set S : Finset (Place ℂ F) := Ti ∪ C.biUnion T with hS_def
  set A : Place ℂ F → Finset ℝ := fun w =>
    (if w ∈ Ti then {δi w} else ∅) ∪ (C.filter (fun c => w ∈ T c)).image (fun c => δ c w)
    with hA_def
  have hA : ∀ w, ∀ x ∈ A w, 0 < x ∧ x < P.ρ w := by
    intro w x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · by_cases hw : w ∈ Ti
      · rw [if_pos hw, Finset.mem_singleton] at hx
        rw [hx]; exact hδi w hw
      · rw [if_neg hw] at hx; exact absurd hx (Finset.notMem_empty _)
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      exact hδ c w (Finset.mem_filter.mp hc).2
  set r : Place ℂ F → ℝ := fun w => if h : (A w).Nonempty then (A w).max' h else 0 with hr_def
  have hr_le : ∀ w x, x ∈ A w → x ≤ r w := by
    intro w x hx
    have hne : (A w).Nonempty := ⟨x, hx⟩
    simp only [hr_def, dif_pos hne]
    exact Finset.le_max' _ _ hx
  have hr : ∀ v ∈ S, 0 ≤ r v ∧ r v < P.ρ v := by
    intro v _
    by_cases h : (A v).Nonempty
    · simp only [hr_def, dif_pos h]
      have hm := hA v _ (Finset.max'_mem _ h)
      exact ⟨hm.1.le, hm.2⟩
    · simp only [hr_def, dif_neg h]
      exact ⟨le_rfl, P.hρ v⟩
  have hAi : ∀ v ∈ Ti, δi v ∈ A v := by
    intro v hv
    simp only [hA_def]
    exact Finset.mem_union_left _ (by rw [if_pos hv]; exact Finset.mem_singleton_self _)
  have hAc : ∀ c ∈ C, ∀ v ∈ T c, δ c v ∈ A v := by
    intro c hc v hv
    simp only [hA_def]
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hv⟩, rfl⟩)
  refine ⟨S, r, hr, fun w' => ?_⟩

  by_cases hfm : f ∈ w'.toValuationSubring
  ·
    set c' : ℂ := w'.evalAt f with hc'_def
    have hpos : 0 < w'.ord (f - algebraMap ℂ F c') :=
      ord_sub_evalAt_pos w' (isRational _) hfm (sub_ne_zero.mpr (hf _))
    by_cases hc' : ‖c'‖ ≤ R
    ·
      have hmem : c' ∈ closedBall (0 : ℂ) R := by rwa [mem_closedBall, dist_zero_right]
      obtain ⟨c, hcC, hc⟩ := mem_iUnion₂.mp (hC hmem)
      have ha : ‖c' - c‖ < ε c := by rwa [mem_ball, dist_eq_norm] at hc
      have hpos' : 0 < w'.ord (f - algebraMap ℂ F c - algebraMap ℂ F (c' - c)) := by
        rwa [map_sub, sub_sub, add_sub_cancel]
      obtain ⟨v, hvT, u, hu, hγu⟩ := hcov c (c' - c) ha w' hpos'
      exact ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcC, hvT⟩), u,
        hu.le.trans (hr_le v _ (hAc c hcC v hvT)), hγu⟩
    ·
      push Not at hc'
      have hRnn : 0 ≤ R := inv_nonneg.mpr hεi.le
      have hc'0 : c' ≠ 0 := by
        intro h; rw [h, norm_zero] at hc'; exact not_lt.mpr hRnn hc'
      have hordf : w'.ord f = 0 := by
        rcases (ord_nonneg_of_mem w' hfm).eq_or_lt with h | h
        · exact h.symm
        · exact absurd (evalAt_eq_zero_of_ord_pos w' hf0 h) hc'0
      have hfim : f⁻¹ ∈ w'.toValuationSubring :=
        mem_of_ord_nonneg _ (inv_ne_zero hf0) (by rw [Place.ord_inv, hordf, neg_zero])
      have hev : w'.evalAt f⁻¹ = c'⁻¹ := by
        have h1 : w'.evalAt f * w'.evalAt f⁻¹ = 1 := by
          rw [← evalAt_mul _ (isRational _) hfm hfim, mul_inv_cancel₀ hf0, Place.evalAt_one]
        exact eq_inv_of_mul_eq_one_right h1
      have hpos'' : 0 < w'.ord (f⁻¹ - algebraMap ℂ F c'⁻¹) := by
        rw [← hev]
        exact ord_sub_evalAt_pos w' (isRational _) hfim (sub_ne_zero.mpr (hfi _))
      have ha : ‖c'⁻¹‖ < εi := by
        rw [norm_inv]; exact inv_lt_of_inv_lt₀ hεi hc'
      obtain ⟨v, hvT, u, hu, hγu⟩ := hcovi c'⁻¹ ha w' hpos''
      exact ⟨v, Finset.mem_union_left _ hvT, u, hu.le.trans (hr_le v _ (hAi v hvT)), hγu⟩
  ·
    have hpos : 0 < w'.ord (f⁻¹ - algebraMap ℂ F 0) := by
      rw [map_zero, sub_zero, Place.ord_inv]
      have := (not_mem_iff_ord_neg w' hf0).mp hfm
      omega
    obtain ⟨v, hvT, u, hu, hγu⟩ := hcovi 0 (by rwa [norm_zero]) w' hpos
    exact ⟨v, Finset.mem_union_left _ hvT, u, hu.le.trans (hr_le v _ (hAi v hvT)), hγu⟩

end Fam

end Family

end AlgebraicCurve.Place.FiniteCover

set_option linter.unusedVariables false in
open AlgebraicCurve.Place.FiniteCover in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (ρ : Place ℂ F → ℝ) (γ : Place ℂ F → ℂ → Place ℂ F) (t : Place ℂ F → F)
    (hρ : ∀ v, 0 < ρ v) (h₀ : ∀ v, γ v 0 = v)
    (ht : ∀ v, ∀ z ∈ Metric.ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1)
    (hγ : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) (ρ v),
        MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)) :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < ρ v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ γ v z = w :=
  Fam.exists_finset_cover (⟨ρ, γ, t, hρ, h₀, ht, hγ⟩ : Fam F)

end
end S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex (solution)
