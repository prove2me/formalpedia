-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingD
-- name    : RPLib_S2_WeilPairingD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:54:29.167592+00:00
-- url     : https://prove2.me/theorems/a263bd3c-00b5-487c-92ad-e34e91edd4d3
-- title:
--   Weil pairing, part D: orders, divisors and the sum identity
-- statement:
--   The order $\mathrm{ord}_P f$ at every point including $O$, the divisor of a function as a finitely supported function, and the identity $\sum_P \mathrm{ord}_P(f)\, P = O$ in the group law.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Sections II.3 and III.3

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingC

/-!
# WPD: orders of functions at points, divisors, the sum identity, constants (unit S2-WeilPairing, O3)

* `ord f P` : the order of `f` at any point `P` of `W⁄L` (including `O`), defined by translating `P` to a fixed
  affine base point; `ord_tau` (translation rule), `ord_eq` (`= -log ν_P f` at affine `P`), `ord_mul`, `ord_inv`.
* `count_spanSingleton` : in a Dedekind domain, `count v (f) = -log v(f)`.
* `hosP`, `exists_hosP`, `hosP_inj` : height-one primes of the coordinate ring = affine points.
* `ord_finite`, `divf` : finite support; the divisor as a finitely supported function.
* `prod_unitP_eq`, `sum_ord_smul` : `(f) = ∏ m_P^{ord_P f}` and `∑ ord_P(f) • P = 0`.
* `exists_const_of_ord` : no zeros or poles at affine points ⇒ constant.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.Weil

section CountVal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

lemma count_span_alg (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a)) =
      -WithZero.log (v.valuation K (algebraMap R K a)) := by
  have hJ : Ideal.span {a} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v hJ,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha,
    WithZero.log_exp, neg_neg]

lemma count_spanSingleton (v : HeightOneSpectrum R) {f : K} (hf : f ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ f) =
      -WithZero.log (v.valuation K f) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haK : algebraMap R K a ≠ 0 := by
    intro h; rw [h, zero_div] at hf; exact hf rfl
  have ha : a ≠ 0 := by rintro rfl; exact haK (map_zero _)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr haK)
      (inv_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hbK)),
    FractionalIdeal.count_inv, count_span_alg v ha, count_span_alg v hb0, map_mul, map_inv₀,
    WithZero.log_mul ((Valuation.ne_zero_iff _).mpr haK)
      (inv_ne_zero ((Valuation.ne_zero_iff _).mpr hbK)), WithZero.log_inv]
  ring

lemma count_ext {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]

end CountVal

section Orders

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
  (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma exists_affine : ∃ P : Pt W L, P ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_y_alg (W.baseChange L) 0
  exact ⟨.some _ _ (equation_iff_nonsingular.mp hb), Point.some_ne_zero _⟩

/-- A fixed affine base point. -/
noncomputable def base : Pt W L := (exists_affine W L).choose

lemma base_ne : base W L ≠ 0 := (exists_affine W L).choose_spec

/-- The order of `f` at a point `P` (any point, including `O`): translate `P` to the base point. -/
noncomputable def ord (f : FF W L) (P : Pt W L) : ℤ :=
  -WithZero.log (nu W L (base W L) (base_ne W L) (tau W L (P - base W L) f))

/-- The height-one prime at an affine point. -/
noncomputable def hosP (P : Pt W L) (hP : P ≠ 0) : HeightOneSpectrum (CR W L) :=
  hos (W.baseChange L) (nonsingular_px_py hP)

variable {W L}

lemma nu_eq_valuation (P : Pt W L) (hP : P ≠ 0) :
    nu W L P hP = (hosP W L P hP).valuation (FF W L) := rfl

lemma ord_tau (S : Pt W L) (f : FF W L) (P : Pt W L) :
    ord W L (tau W L S f) P = ord W L f (P + S) := by
  have e : P - base W L + S = P + S - base W L := by abel
  rw [ord, ord, ← e, tau_add_apply]

lemma ord_eq {P : Pt W L} (hP : P ≠ 0) (f : FF W L) :
    ord W L f P = -WithZero.log (nu W L P hP f) := by
  have e : base W L + (P - base W L) = P := by abel
  have hT : base W L + (P - base W L) ≠ 0 := by rw [e]; exact hP
  rw [ord, nu_tau (base W L) (P - base W L) (base_ne W L) hT f, nu_congr e hT hP]

lemma tau_ne_zero (S : Pt W L) {f : FF W L} (hf : f ≠ 0) : tau W L S f ≠ 0 :=
  (_root_.map_ne_zero (tau W L S)).mpr hf

lemma ord_mul {f g : FF W L} (hf : f ≠ 0) (hg : g ≠ 0) (P : Pt W L) :
    ord W L (f * g) P = ord W L f P + ord W L g P := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).mpr (tau_ne_zero _ hf))
    ((Valuation.ne_zero_iff _).mpr (tau_ne_zero _ hg))]
  ring

lemma ord_inv (f : FF W L) (P : Pt W L) : ord W L f⁻¹ P = -ord W L f P := by
  simp only [ord, map_inv₀, WithZero.log_inv, neg_neg]

lemma ord_div {f g : FF W L} (hf : f ≠ 0) (hg : g ≠ 0) (P : Pt W L) :
    ord W L (f / g) P = ord W L f P - ord W L g P := by
  rw [div_eq_mul_inv, ord_mul hf (inv_ne_zero hg), ord_inv]; ring

lemma ord_pow (f : FF W L) (n : ℕ) (P : Pt W L) : ord W L (f ^ n) P = n * ord W L f P := by
  simp only [ord, map_pow, WithZero.log_pow, nsmul_eq_mul]; ring

lemma ord_alg {c : L} (hc : c ≠ 0) (P : Pt W L) : ord W L (algebraMap L (FF W L) c) P = 0 := by
  rw [ord, AlgEquiv.commutes, nu_alg_eq_one hc, WithZero.log_one, neg_zero]

lemma ord_one (P : Pt W L) : ord W L 1 P = 0 := by
  simpa using ord_alg (W := W) (L := L) one_ne_zero P

lemma nu_eq_one_of_ord {P : Pt W L} (hP : P ≠ 0) {f : FF W L} (hf : f ≠ 0)
    (h : ord W L f P = 0) : nu W L P hP f = 1 := by
  rw [ord_eq hP, neg_eq_zero] at h
  rw [← WithZero.exp_log ((Valuation.ne_zero_iff (nu W L P hP)).mpr hf), h, WithZero.exp_zero]

/-! ### Height-one primes = affine points -/

lemma count_hosP {P : Pt W L} (hP : P ≠ 0) {f : FF W L} (hf : f ≠ 0) :
    FractionalIdeal.count (FF W L) (hosP W L P hP)
      (FractionalIdeal.spanSingleton (CR W L)⁰ f) = ord W L f P := by
  rw [count_spanSingleton _ hf, ord_eq hP]; rfl

lemma exists_hosP (v : HeightOneSpectrum (CR W L)) : ∃ (P : Pt W L) (hP : P ≠ 0), hosP W L P hP = v := by
  obtain ⟨x, y, h, hv⟩ := exists_eq_XYIdeal (W.baseChange L) v.asIdeal
  exact ⟨.some _ _ h, Point.some_ne_zero h, HeightOneSpectrum.ext hv.symm⟩

/-- The fractional ideal `m_P` as a unit (`1` at `O`). -/
noncomputable def unitP (P : Pt W L) : (FractionalIdeal (CR W L)⁰ (FF W L))ˣ :=
  if h : P = 0 then 1 else XYIdeal' (W := (W.baseChange L).toAffine) (nonsingular_px_py h)

lemma unitP_coe {P : Pt W L} (hP : P ≠ 0) :
    (unitP P : FractionalIdeal (CR W L)⁰ (FF W L)) = ((hosP W L P hP).asIdeal : FractionalIdeal _ _) := by
  rw [unitP, dif_neg hP]; rfl

lemma toClass_eq (P : Pt W L) :
    Point.toClass P = Additive.ofMul (ClassGroup.mk (FF W L) (unitP P)) := by
  by_cases hP : P = 0
  · subst hP
    rw [map_zero, unitP, dif_pos rfl, map_one]; rfl
  · conv_lhs => rw [eq_some_px_py hP]
    rw [Point.toClass_some, unitP, dif_neg hP]; rfl

lemma hosP_inj {P Q : Pt W L} (hP : P ≠ 0) (hQ : Q ≠ 0) (h : hosP W L P hP = hosP W L Q hQ) :
    P = Q := by
  apply Point.toClass_injective
  have hu : unitP P = unitP Q := Units.ext (by rw [unitP_coe hP, unitP_coe hQ, h])
  rw [toClass_eq, toClass_eq, hu]

/-- The affine point of a height-one prime. -/
noncomputable def ptOf (v : HeightOneSpectrum (CR W L)) : Pt W L := (exists_hosP v).choose

lemma ptOf_ne (v : HeightOneSpectrum (CR W L)) : ptOf v ≠ 0 := (exists_hosP v).choose_spec.choose

lemma hosP_ptOf (v : HeightOneSpectrum (CR W L)) : hosP W L (ptOf v) (ptOf_ne v) = v :=
  (exists_hosP v).choose_spec.choose_spec

lemma ptOf_hosP {P : Pt W L} (hP : P ≠ 0) : ptOf (hosP W L P hP) = P :=
  hosP_inj (ptOf_ne _) hP (hosP_ptOf _)

lemma count_unitP_self {P : Pt W L} (hP : P ≠ 0) :
    FractionalIdeal.count (FF W L) (hosP W L P hP) (unitP P : FractionalIdeal (CR W L)⁰ (FF W L)) = 1 := by
  rw [unitP_coe hP, FractionalIdeal.count_self]

lemma count_unitP_ne {P Q : Pt W L} (hP : P ≠ 0) (hQP : Q ≠ P) :
    FractionalIdeal.count (FF W L) (hosP W L P hP) (unitP Q : FractionalIdeal (CR W L)⁰ (FF W L)) = 0 := by
  by_cases hQ : Q = 0
  · rw [unitP, dif_pos hQ, Units.val_one, FractionalIdeal.count_one]
  · rw [unitP_coe hQ, FractionalIdeal.count_maximal_coprime]
    intro h; exact hQP (hosP_inj hQ hP h)

lemma count_prod_unitP (v : HeightOneSpectrum (CR W L)) (Z : Finset (Pt W L)) (n : Pt W L → ℤ) :
    FractionalIdeal.count (FF W L) v
      ((∏ Q ∈ Z, unitP Q ^ n Q : (FractionalIdeal (CR W L)⁰ (FF W L))ˣ) :
        FractionalIdeal (CR W L)⁰ (FF W L)) =
      ∑ Q ∈ Z, n Q * FractionalIdeal.count (FF W L) v
        (unitP Q : FractionalIdeal (CR W L)⁰ (FF W L)) := by
  rw [Units.coe_prod, FractionalIdeal.count_prod _ _ _ _ (fun Q _ => Units.ne_zero _)]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow]

/-- `count` at an affine point of `∏_{Q ∈ Z} m_Q ^ n_Q`. -/
lemma count_hosP_prod {P : Pt W L} (hP : P ≠ 0) (Z : Finset (Pt W L)) (n : Pt W L → ℤ)
    (hZ : ∀ Q, Q ≠ 0 → n Q ≠ 0 → Q ∈ Z) :
    FractionalIdeal.count (FF W L) (hosP W L P hP)
      ((∏ Q ∈ Z, unitP Q ^ n Q : (FractionalIdeal (CR W L)⁰ (FF W L))ˣ) :
        FractionalIdeal (CR W L)⁰ (FF W L)) = n P := by
  rw [count_prod_unitP]
  by_cases hPZ : P ∈ Z
  · rw [Finset.sum_eq_single_of_mem P hPZ (fun Q _ hQP => by rw [count_unitP_ne hP hQP, mul_zero]),
      count_unitP_self hP, mul_one]
  · rw [Finset.sum_eq_zero (fun Q hQ => by
      rw [count_unitP_ne hP (fun h => hPZ (h ▸ hQ)), mul_zero])]
    by_contra h
    exact hPZ (hZ P hP (Ne.symm h))

/-! ### Finite support and the divisor -/

lemma ord_finite {f : FF W L} (hf : f ≠ 0) : (Function.support (ord W L f)).Finite := by
  have hfin := FractionalIdeal.finite_factors (K := FF W L)
    (FractionalIdeal.spanSingleton (CR W L)⁰ f)
  rw [Filter.eventually_cofinite] at hfin
  refine ((hfin.image ptOf).insert 0).subset ?_
  intro P hP
  by_cases h0 : P = 0
  · exact Or.inl h0
  · right
    refine ⟨hosP W L P h0, ?_, ptOf_hosP h0⟩
    show ¬ _ = _
    rw [count_hosP h0 hf]
    exact hP

/-- The divisor of `f` (`0` for `f = 0`). -/
noncomputable def divf (f : FF W L) : Pt W L →₀ ℤ :=
  if hf : f = 0 then 0 else Finsupp.ofSupportFinite (ord W L f) (ord_finite hf)

lemma divf_apply {f : FF W L} (hf : f ≠ 0) (P : Pt W L) : divf f P = ord W L f P := by
  rw [divf, dif_neg hf]; rfl

lemma mem_support_divf {f : FF W L} (hf : f ≠ 0) {P : Pt W L} (hP : ord W L f P ≠ 0) :
    P ∈ (divf f).support := by
  rw [Finsupp.mem_support_iff, divf_apply hf]; exact hP

/-! ### The principal ideal and the sum identity -/

lemma prod_unitP_eq {f : FF W L} (hf : f ≠ 0) (Z : Finset (Pt W L))
    (hZ : ∀ P, P ≠ 0 → ord W L f P ≠ 0 → P ∈ Z) :
    ((∏ Q ∈ Z, unitP Q ^ ord W L f Q : (FractionalIdeal (CR W L)⁰ (FF W L))ˣ) :
      FractionalIdeal (CR W L)⁰ (FF W L)) = FractionalIdeal.spanSingleton (CR W L)⁰ f := by
  apply count_ext (Units.ne_zero _) (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hf)
  intro v
  obtain ⟨P, hP, rfl⟩ := exists_hosP v
  rw [count_hosP_prod hP Z _ hZ, count_hosP hP hf]

lemma mk_prod_unitP {f : FF W L} (hf : f ≠ 0) (Z : Finset (Pt W L))
    (hZ : ∀ P, P ≠ 0 → ord W L f P ≠ 0 → P ∈ Z) :
    ClassGroup.mk (FF W L) (∏ Q ∈ Z, unitP Q ^ ord W L f Q) = 1 := by
  rw [ClassGroup.mk_eq_one_iff, prod_unitP_eq hf Z hZ, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨f, rfl⟩⟩

lemma toClass_sum (Z : Finset (Pt W L)) (n : Pt W L → ℤ) :
    Point.toClass (∑ P ∈ Z, n P • P) =
      Additive.ofMul (ClassGroup.mk (FF W L) (∏ Q ∈ Z, unitP Q ^ n Q)) := by
  rw [map_sum, map_prod, ofMul_prod]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [map_zsmul, toClass_eq, map_zpow, ofMul_zpow]

/-- **Sum identity**: `∑ ord_P(f) • P = 0` (over any finite set containing the affine support). -/
theorem sum_ord_smul {f : FF W L} (hf : f ≠ 0) (Z : Finset (Pt W L))
    (hZ : ∀ P, P ≠ 0 → ord W L f P ≠ 0 → P ∈ Z) : ∑ P ∈ Z, ord W L f P • P = 0 := by
  apply Point.toClass_injective
  rw [toClass_sum, mk_prod_unitP hf Z hZ, map_zero]; rfl

/-! ### Constants -/

/-- A nonzero function with no zeros or poles at affine points is a constant. -/
theorem exists_const_of_ord {f : FF W L} (hf : f ≠ 0) (h : ∀ P : Pt W L, P ≠ 0 → ord W L f P = 0) :
    ∃ c : L, c ≠ 0 ∧ f = algebraMap L (FF W L) c := by
  have hv : ∀ g : FF W L, g ≠ 0 → (∀ P : Pt W L, P ≠ 0 → ord W L g P = 0) →
      ∀ v : HeightOneSpectrum (CR W L), v.valuation (FF W L) g ≤ 1 := by
    intro g hg hg' v
    obtain ⟨P, hP, rfl⟩ := exists_hosP v
    exact (nu_eq_one_of_ord hP hg (hg' P hP)).le
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := CR W L) (K := FF W L)
    f (hv f hf h)
  obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := CR W L) (K := FF W L)
    f⁻¹ (hv f⁻¹ (inv_ne_zero hf) (fun P hP => by rw [ord_inv, h P hP, neg_zero]))
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective (CR W L) (FF W L)
    rw [map_mul, hr, hs, map_one, mul_inv_cancel₀ hf]
  have hN : IsUnit (Algebra.norm L[X] r) := (IsUnit.of_mul_eq_one s hrs).map _
  obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq r
  have h0 := degree_eq_zero_of_isUnit hN
  rw [degree_norm_smul_basis] at h0
  have hq : q = 0 := by
    by_contra hq0
    have h3 : 2 • q.degree + 3 ≤ 0 := h0 ▸ le_max_right _ _
    rw [degree_eq_natDegree hq0] at h3
    have h4 : ((2 • q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
      first
      | exact_mod_cast h3
      | (push_cast; exact h3)
      | exact h3
    have := WithBot.coe_le_coe.mp h4
    simp only [Nat.cast_id, smul_eq_mul] at this
    omega
  subst hq
  have hN2 : Algebra.norm L[X] (p • (1 : CR W L) + (0 : L[X]) • mk (W.baseChange L).toAffine Y) =
      p ^ 2 := by
    rw [norm_smul_basis]; ring
  rw [hN2, isUnit_pow_iff two_ne_zero] at hN
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hN
  refine ⟨c, hc.ne_zero, ?_⟩
  rw [← hr, zero_smul, add_zero, Algebra.smul_def, mul_one]
  exact alg_mk_CC W L c

end Orders

end RPLib.Weil


