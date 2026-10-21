-- Prove2me | Definitions.Def_RiemannRoch_GenusCharts
-- name    : RiemannRoch_GenusCharts
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T12:33:05.221914+00:00
-- url     : https://prove2.me/theorems/d51e86bb-1551-45ca-b9a1-8faa1fe7e7a8
-- title:
--   Genus of a function field and index of speciality (chart presentation)
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation, $\deg P=\dim_k(\mathcal O/P)$ for the relevant Dedekind domain $\mathcal O$, and a chart divisor is a finitely supported $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$ with $\deg D=\sum_P D(P)\deg P$. In this file $k$ is moreover assumed to be the full constant field of $K$ where needed, $\mathcal L(D)$, $\ell(D)$, $\mathcal A_K$, $\mathcal A_K(D)$, $\widetilde K$ are as in the previous files, $x_K\in K$ is the image of $X$, and $(x)_\infty$ is the pole divisor (file `RiemannRoch_IntrinsicAdeles`).
--
--   This file introduces:
--
--   1. the local parameter $t=1/X\in\mathcal O_\infty$ and its image $t_K\in K$;
--   2. the ramification index $e(P|\mathfrak m_\infty)$ of a prime $P$ of $\mathcal O_{K,\infty}$ over $\mathfrak m_\infty$, and the ideal of $\mathcal O_{K,\infty}$ attached to a chart place (the prime itself for an infinite place, $0$ for a finite one);
--   3. the **defect** $\delta(D)=\deg D+1-\ell(D)$ and the **genus**
--   $$g=\max_{D}\big(\deg D+1-\ell(D)\big)\in\mathbb Z_{\ge0},$$
--   the maximum over all chart divisors $D$;
--   4. the **index of speciality** $i(D)=\ell(D)-\deg D-1+g$, and the dimension $\dim_k\mathcal A_K/(\mathcal A_K(D)+\widetilde K)$.
--
--   It also contains the structural lemmas needed to show that the maximum defining $g$ exists: $\mathfrak m_\infty=(t)$ and $\mathfrak m_\infty\mathcal O_{K,\infty}=t\,\mathcal O_{K,\infty}$; $x_Kt_K=1$ and $x_K\in\mathcal O_K$; $(x_K)_\infty$ vanishes at finite places and equals $e(P|\mathfrak m_\infty)\ge1$ at an infinite place $P$, where $v_P(t_K)=e(P|\mathfrak m_\infty)=-v_P(x_K)$; the identity and bound
--   $$\deg(x_K)_\infty=\sum_{P\mid\mathfrak m_\infty}e(P|\mathfrak m_\infty)\,f(P|\mathfrak m_\infty)\le[K:k(X)],$$
--   with equality $\deg(x_K)_\infty=[K:k(X)]$ when $k$ is the full constant field; invariance of $\delta$ under adding principal divisors and its monotonicity; a bound $\delta(D)\le\deg B+1-[K:k(X)]$ for all $D$, with $B$ the pole bound of a basis of $K/k(X)$; and Riemann's inequality $\ell(D)\ge\deg D+1-g$, with equality $\delta(D)=g$ for some $D$.
--
--   The genus is the fundamental invariant of the function field; the index of speciality is the correction term in the Riemann–Roch formula $\ell(D)=\deg D+1-g+i(D)$. In the chain of definition files it imports `RiemannRoch_IntrinsicAdeles` and is imported by `RiemannRoch_FilterChain1`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The full-constant-field hypothesis is `[IsFullConstantField k K]`, declared for the whole file but omitted from the lemmas that do not need it. The genus `FunctionField.Chart.genus k K : ℕ` is defined by choice from the existence of a maximal defect over chart divisors (`DivisorA k K`); `indexOfSpecialty` is the natural number $(\ell(D)-(\deg D+1-g))$, nonnegative by Riemann's inequality. The ramification index is Mathlib's `Ideal.ramificationIdx'` and the sum runs over `IsDedekindDomain.primesOverFinset`.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4: pole divisor and Theorem 1.4.11 ($\deg(x)_\infty=[F:K(x)]$), Definition 1.4.15 (genus as maximal $\deg A-\ell(A)+1$), Riemann's theorem and the index of speciality $i(A)=\ell(A)-\deg A+g-1$; ramification at infinity: Section 3.1 (fundamental equality, cf.). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Genus/Ramification.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Genus/Basic.lean

import Mathlib
import Definitions.Def_RiemannRoch_IntrinsicAdeles

/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

set_option linter.style.haveILetI false

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero Additive
open Polynomial BigOperators Submodule IntermediateField Ideal FunctionField
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [IsFullConstantField k K]
local instance instDecidableEqPlaceARam : DecidableEq (PlaceA k K) := Classical.decEq _
local instance instDecidableEqRatFuncRam : DecidableEq k⟮X⟯ := Classical.decEq _
noncomputable def tRatFunc : k⟮X⟯ := 1 / RatFunc.X
noncomputable def tA : inftyValuationSubring k :=
  ⟨tRatFunc k, by
    rw [Valuation.mem_valuationSubring_iff]
    dsimp [tRatFunc]
    rw [RatFunc.inftyValuation.X_inv k]
    exact WithZero.exp_le_exp.mpr (show (-1 : ℤ) ≤ 0 by omega)⟩
@[simp]
theorem tRatFunc_coe : (tA k : k⟮X⟯) = tRatFunc k := rfl
omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem maximalIdeal_infty_eq_span_t :
    IsLocalRing.maximalIdeal (inftyValuationSubring k) =
      Ideal.span {(tA k : inftyValuationSubring k)} := by
  let v := RatFunc.inftyValuation k
  have hπval : v (tRatFunc k) = WithZero.exp (-1 : ℤ) := RatFunc.inftyValuation.X_inv k
  have hgen : (↑(Valuation.IsRankOneDiscrete.generator v) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
    have h := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      (v := v) (show WithZero.exp (-1 : ℤ) ∈ Set.range v from ⟨tRatFunc k, hπval⟩)
    exact congrArg Units.val h
  have hπ : v.IsUniformizer (tA k : k⟮X⟯) := by
    rw [Valuation.IsUniformizer.iff, tRatFunc_coe k, hgen]
    exact hπval
  exact Valuation.IsUniformizer.is_generator hπ
local notation "inftyRing" => inftyValuationSubring k
local notation "inftyInts" => infiniteIntegers k K
local notation "maxIdealInfty" => IsLocalRing.maximalIdeal (inftyValuationSubring k)
noncomputable def ramIdxInfty (P : Ideal (infiniteIntegers k K)) : ℕ :=
  (IsLocalRing.maximalIdeal (inftyValuationSubring k)).ramificationIdx' P
noncomputable def tK : K := algebraMap k⟮X⟯ K (tRatFunc k)
omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem map_maximalIdeal_infty :
    Ideal.map (algebraMap inftyRing inftyInts) maxIdealInfty =
      Ideal.span {algebraMap inftyRing inftyInts (tA k)} := by
  rw [maximalIdeal_infty_eq_span_t k, Ideal.map_span, Set.image_singleton]
omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem XK_mul_tK : XK k K * tK k K = 1 := by
  dsimp only [XK, tK, tRatFunc]
  rw [← map_mul (algebraMap k⟮X⟯ K), div_eq_mul_inv, one_mul,
    mul_inv_cancel₀ RatFunc.X_ne_zero, map_one]
omit [Algebra k K] [IsScalarTower k k[X] K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem XK_mem_ringOfIntegers :
    ∃ a : ringOfIntegers k K, (a : K) = XK k K := by
  have hx : (algebraMap k[X] K (Polynomial.X : k[X])) ∈ ringOfIntegers k K :=
    (mem_integralClosure_iff (R := k[X]) (A := K)).2
      (isIntegral_algebraMap (x := (Polynomial.X : k[X])))
  refine ⟨⟨algebraMap k[X] K (Polynomial.X : k[X]), hx⟩, ?_⟩
  dsimp [XK]
  rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, RatFunc.algebraMap_X]
omit [Algebra k K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem ringOfIntegers_coe_ne_zero {a : ringOfIntegers k K} (ha : a ≠ 0) : (a : K) ≠ 0 :=
  fun h => ha ((Subtype.ext_iff).mpr h)
omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem principalDivisorA_nonneg_at_finite_of_mem_ringOfIntegers {a : ringOfIntegers k K}
    (ha : a ≠ 0) (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    0 ≤ principalDivisorA k K
      (Additive.ofMul (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) (Sum.inl w) := by
  rw [principalDivisorA_apply_finite, FractionalIdeal.principalDivisor_apply]
  have hle := w.valuation_le_one (K := K) a
  have hval := FractionalIdeal.valuation_eq_exp_neg_count (R := ringOfIntegers k K) (K := K) w
    (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))
  have hcount :
      FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K)
        (Additive.ofMul (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) w =
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (ringOfIntegers k K)⁰
          (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) := by
    rfl
  have hnonneg :
      0 ≤ FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (ringOfIntegers k K)⁰
          (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha))) := by
    let count :=
      FractionalIdeal.count K w
        (FractionalIdeal.spanSingleton (ringOfIntegers k K)⁰
          (Units.mk0 (a : K) (ringOfIntegers_coe_ne_zero k K ha)))
    have hle' : -count ≤ 0 :=
      WithZero.exp_le_exp.mp (by rw [← hval, WithZero.exp_zero]; exact hle)
    exact neg_nonpos.mp hle'
  simpa [hcount] using hnonneg
omit [IsFullConstantField k K] in
theorem polarDivisor_XK_zero_at_finite
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    polarDivisor k K (XK k K) (Sum.inl w) = 0 := by
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  obtain ⟨a, ha⟩ := XK_mem_ringOfIntegers k K
  have ha0 : a ≠ 0 := fun ha0 => hx0 (by simpa [ha] using congrArg Subtype.val ha0)
  have hprincipal :
      0 ≤ principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0)) (Sum.inl w) := by
    simpa [ha] using
      principalDivisorA_nonneg_at_finite_of_mem_ringOfIntegers (k := k) (K := K) ha0 w
  unfold polarDivisor
  simp only [dif_neg hx0, Finsupp.sup_apply]
  exact max_eq_right (neg_nonpos.mpr hprincipal)
omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem tK_ne_zero : tK k K ≠ 0 := by
  dsimp [tK, tRatFunc]
  intro h
  rw [← map_zero (algebraMap k⟮X⟯ K)] at h
  exact one_div_ne_zero RatFunc.X_ne_zero <|
    (RingHom.injective (algebraMap k⟮X⟯ K)).eq_iff.mp h
omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem principalDivisorA_tK_at_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K (Additive.ofMul (Units.mk0 (tK k K) (tK_ne_zero k K))) (Sum.inr v) =
      (ramIdxInfty k K v.asIdeal : ℤ) := by
  rw [principalDivisorA_apply_infinite]
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let tS : S := algebraMap A S (tA k)
  have htK : tK k K = algebraMap A K (tA k) := by
    dsimp [tK, tA, tRatFunc]
    rfl
  have hspan :
      FractionalIdeal.spanSingleton S⁰ (tK k K) =
        (Ideal.span {tS} : FractionalIdeal S⁰ K) := by
    rw [htK, IsScalarTower.algebraMap_apply A S K, ← FractionalIdeal.coeIdeal_span_singleton]
  have htS : tS ≠ 0 := by
    intro h
    have hz : tK k K = 0 := by
      dsimp [tS] at h
      rw [htK, IsScalarTower.algebraMap_apply A S K, h, map_zero]
    exact tK_ne_zero k K hz
  let p := IsLocalRing.maximalIdeal A
  have hinj := ValuationSubring.integralClosure_algebraMap_injective
    (v := RatFunc.inftyValuation k) (L := K)
  have hpne : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  have hmap : Ideal.map (algebraMap A S) p ≠ ⊥ := by
    rintro hbot
    exact hpne ((Ideal.map_eq_bot_iff_of_injective hinj).mp hbot)
  have hcount :
      FractionalIdeal.principalDivisor (R := S) (K := K)
          (Additive.ofMul (Units.mk0 (tK k K) (tK_ne_zero k K))) v =
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (algebraMap A S) p)).count
          v.asIdeal := by
    rw [FractionalIdeal.principalDivisor_apply, toMul_ofMul, Units.val_mk0, hspan,
      FractionalIdeal.count_coe (K := K) v (Ideal.span_singleton_eq_bot.not.mpr htS),
      ← map_maximalIdeal_infty k]
    rw [Ideal.count_associates_factors_eq hmap v.isPrime v.ne_bot]
  rw [hcount, ← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime
      v.ne_bot, ramIdxInfty]
omit [IsFullConstantField k K] in
theorem principalDivisorA_XK_at_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) (XK_ne_zero k K))) (Sum.inr v) =
      -(ramIdxInfty k K v.asIdeal : ℤ) := by
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  have ht0 : tK k K ≠ 0 := tK_ne_zero k K
  let hunit : Kˣ := Units.mk0 (XK k K * tK k K) (by rw [XK_mul_tK k K]; exact one_ne_zero)
  have hmul : hunit = Units.mk0 (XK k K) hx0 * Units.mk0 (tK k K) ht0 := by
    apply Units.ext
    simp [hunit, Units.val_mul, Units.val_mk0, XK_mul_tK k K]
  have hprod :
      principalDivisorA k K (Additive.ofMul hunit) =
        principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0)) +
          principalDivisorA k K (Additive.ofMul (Units.mk0 (tK k K) ht0)) := by
    rw [show Additive.ofMul hunit =
        Additive.ofMul (Units.mk0 (XK k K) hx0 * Units.mk0 (tK k K) ht0) from congr_arg _ hmul,
      ofMul_mul, (principalDivisorA k K).map_add]
  have hone : principalDivisorA k K (Additive.ofMul hunit) = 0 := by
    ext w
    simp only [Finsupp.zero_apply]
    have hv := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul hunit) w
    have hval' : placeValuation k K w ↑(Additive.toMul (Additive.ofMul hunit)) = 1 := by
      rw [toMul_ofMul, show (↑hunit : K) = 1 by simp [hunit, XK_mul_tK k K]]
      rcases w with w | w <;> simp [placeValuation]
    have hexp :
        WithZero.exp (-((principalDivisorA k K) (Additive.ofMul hunit)) w) = WithZero.exp 0 :=
      (hv.symm.trans hval').trans WithZero.exp_zero.symm
    exact neg_eq_zero.mp (WithZero.exp_injective hexp)
  have hzero :
      principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0)) (Sum.inr v) +
          principalDivisorA k K (Additive.ofMul (Units.mk0 (tK k K) ht0)) (Sum.inr v) = 0 := by
    have := congrArg (fun D => D (Sum.inr v)) hone
    rwa [hprod] at this
  rw [principalDivisorA_tK_at_infinite k K v] at hzero
  linarith
omit [Algebra k K] [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [IsFullConstantField k K] in
theorem ramificationIdx_pos_over_infty
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    0 < ramIdxInfty k K v.asIdeal := by
  let A := inftyValuationSubring k
  let p := IsLocalRing.maximalIdeal A
  have hpne : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  have hPp : v.asIdeal.LiesOver p := ⟨(IsLocalRing.eq_maximalIdeal inferInstance).symm⟩
  exact Nat.cast_pos.mpr <|
    Nat.pos_iff_ne_zero.mpr <|
      IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver (S := infiniteIntegers k K)
        v.asIdeal hpne
omit [IsFullConstantField k K] in
theorem polarDivisor_XK_at_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    polarDivisor k K (XK k K) (Sum.inr v) = ramIdxInfty k K v.asIdeal := by
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  have hprincipal := principalDivisorA_XK_at_infinite (k := k) (K := K) v
  have hpos : 0 < (ramIdxInfty k K v.asIdeal : ℤ) :=
    Nat.cast_pos.mpr (ramificationIdx_pos_over_infty (k := k) (K := K) v)
  have hneg :
      (-principalDivisorA k K (Additive.ofMul (Units.mk0 (XK k K) hx0))) (Sum.inr v) =
        (ramIdxInfty k K v.asIdeal : ℤ) := by
    simpa using congrArg Neg.neg hprincipal
  unfold polarDivisor
  simp only [dif_neg hx0, Finsupp.sup_apply, hneg]
  exact max_eq_left (le_of_lt hpos)
noncomputable def inftyIdealOfPlace (v : PlaceA k K) : Ideal (infiniteIntegers k K) :=
  match v with
  | Sum.inr w => w.asIdeal
  | Sum.inl _ => ⊥
omit [IsFullConstantField k K] in
theorem deg_polarDivisor_XK_eq_primesOverFinset_sum :
    deg k K (polarDivisor k K (XK k K)) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset
          (IsLocalRing.maximalIdeal (inftyValuationSubring k)) (infiniteIntegers k K),
        (ramIdxInfty k K P : ℤ) *
          ((IsLocalRing.maximalIdeal (inftyValuationSubring k)).inertiaDeg' P : ℤ) := by
  classical
  rw [deg, Finsupp.sum]
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p := IsLocalRing.maximalIdeal A
  let D := polarDivisor k K (XK k K)
  have hp : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  let pred : PlaceA k K → Prop := fun v => match v with | Sum.inr _ => true | _ => false
  let g : PlaceA k K → ℤ := fun v => (D v : ℤ) * (placeDegree k K v : ℤ)
  have hsum_filter :
      D.support.sum g =
        (D.support.filter pred).sum g :=
    Eq.symm <|
      Finset.sum_subset (Finset.filter_subset pred D.support) fun v hv hv' => by
        rcases v with v | v
        · rw [polarDivisor_XK_zero_at_finite, zero_mul]
        · exfalso
          simp only [Finset.mem_filter, pred] at hv'
          exact hv' ⟨hv, by simp⟩
  rw [hsum_filter]
  apply Finset.sum_bij (fun v _ => inftyIdealOfPlace (k := k) (K := K) v)
  · intro v hv
    simp only [Finset.mem_filter, pred] at hv
    obtain ⟨_, hright⟩ := hv
    rcases v with v | w
    · cases hright
    · rw [IsDedekindDomain.mem_primesOverFinset_iff hp]
      have hpw : p = w.asIdeal.under A :=
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A w.asIdeal)).symm
      exact ⟨w.isPrime, ⟨hpw⟩⟩
  · intro v₁ hv₁ v₂ hv₂ h
    simp only [Finset.mem_filter, pred] at hv₁ hv₂ ⊢
    match v₁ with
    | Sum.inl _ => simp at hv₁
    | Sum.inr w₁ =>
      match v₂ with
      | Sum.inl _ => simp at hv₂
      | Sum.inr w₂ =>
        simp only [inftyIdealOfPlace] at h
        exact congrArg Sum.inr (IsDedekindDomain.HeightOneSpectrum.ext h)
  · intro P hP
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff hp (P := P)).mp hP
    have hprime : P.IsPrime := hmem.1
    have hbot : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp hmem
    let w : IsDedekindDomain.HeightOneSpectrum S := ⟨P, hprime, hbot⟩
    refine ⟨Sum.inr w, ?_, rfl⟩
    · simp only [Finset.mem_filter, pred, Finsupp.mem_support_iff]
      refine And.intro ?_ (by simp)
      rw [polarDivisor_XK_at_infinite]
      norm_cast
      exact (ramificationIdx_pos_over_infty k K w).ne'
  · intro v hv
    simp only [Finset.mem_filter, pred, inftyIdealOfPlace] at hv ⊢
    rcases v with v | v
    · simp at hv
    · have hpw : v.asIdeal.under A = p :=
        IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A v.asIdeal)
      rw [polarDivisor_XK_at_infinite k K v, ramIdxInfty, placeDegree_infinite_eq_inertiaDeg, hpw]
omit [IsFullConstantField k K] in
theorem deg_polarX_le_finrank :
    deg k K (polarDivisor k K (XK k K)) ≤ Module.finrank k⟮X⟯ K := by
  rw [deg_polarDivisor_XK_eq_primesOverFinset_sum k K]
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p := IsLocalRing.maximalIdeal A
  have hp : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A)
      (IsDiscreteValuationRing.not_isField A)
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  have hsum := Ideal.sum_ramification_inertia (R := A) (S := S) (K := k⟮X⟯) (L := K) hp
  have heq :
      (∑ P ∈ IsDedekindDomain.primesOverFinset p S,
          (ramIdxInfty k K P : ℤ) * (p.inertiaDeg' P : ℤ)) =
        Module.finrank k⟮X⟯ K := by
    dsimp [ramIdxInfty]
    norm_cast
  exact le_of_eq heq
end FunctionField.Chart
end
end
end

section
section
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
variable [IsFullConstantField k K]
local instance instDecidableEqRatFuncGenus : DecidableEq k⟮X⟯ := Classical.decEq _
noncomputable def defect (D : DivisorA k K) : ℤ :=
  deg k K D + 1 - ell k K D
theorem deg_polarX_eq_finrank :
    deg k K (polarDivisor k K (XK k K)) = Module.finrank k⟮X⟯ K := by
  exact le_antisymm (deg_polarX_le_finrank (k := k) (K := K))
    (finrank_le_deg_polarX (k := k) (K := K))
section RiemannFamily
omit [IsFullConstantField k K] in
theorem defect_mono' {D D' : DivisorA k K} (h : D ≤ D') :
    defect k K D ≤ defect k K D' := by
  dsimp only [defect]
  have := defect_mono (k := k) (K := K) h
  omega
omit [IsFullConstantField k K] in
theorem defect_add_principal (D : DivisorA k K) (x : Kˣ) :
    defect k K (D + principalDivisorA k K (Additive.ofMul x)) = defect k K D := by
  dsimp only [defect]
  rw [deg_add, deg_principalDivisor_eq_zero (k := k) (K := K) x, ell_add_principal, add_zero]
omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem le_add_principal_of_memRRspace {D₀ D₁ : DivisorA k K} {f : K} (hf : f ≠ 0)
    (hmem : memRRspace k K (D₁ - D₀) f) :
    D₀ ≤ D₁ + principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) := by
  rw [le_iff_sub_effective]
  intro v
  dsimp only [Finsupp.add_apply, Finsupp.sub_apply]
  have hv := hmem v
  have hxval := placeValuation_eq_exp_neg_principalDivisor k K (Additive.ofMul (Units.mk0 f hf)) v
  change placeValuation k K v f ≤ WithZero.exp ((D₁ - D₀) v) at hv
  change placeValuation k K v f =
    WithZero.exp (-(principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) v)) at hxval
  rw [hxval] at hv
  have hexp := WithZero.exp_le_exp.mp hv
  have hsubv : (D₁ - D₀) v = D₁ v - D₀ v := rfl
  have hexp' :
      -(principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) v) ≤ D₁ v - D₀ v := by
    simpa [hsubv] using hexp
  linarith
omit [IsFullConstantField k K] in
theorem ell_sub_effective_sub_ge {D E : DivisorA k K} (hE : IsEffective k K E) :
    (ell k K (D + E) : ℤ) - deg k K E ≤ ell k K D := by
  have hle : D ≤ D + E := by
    intro v
    simp only [Finsupp.add_apply]
    linarith [hE v]
  have hsum := finrankRRspaceDiff_add_ell (k := k) (K := K) hle
  have hq := finrankRRspaceDiff_add_effective_le (k := k) (K := K) D E hE
  have hdeg : 0 ≤ deg k K E := deg_nonneg (k := k) (K := K) hE
  have htoNat : ((deg k K E).toNat : ℤ) = deg k K E := Int.toNat_of_nonneg hdeg
  have hqZ : (finrankRRspaceDiff k K D (D + E) : ℤ) ≤ deg k K E := by
    rw [← htoNat]
    exact_mod_cast hq
  have hsum' : (finrankRRspaceDiff k K D (D + E) : ℤ) + ell k K D = ell k K (D + E) := by
    exact_mod_cast hsum
  omega
omit [IsFullConstantField k K] in
theorem defect_le_of_family (B C : DivisorA k K) (c₀ : ℤ)
    (hmono : ∀ r : ℕ, defect k K (C + r • B) ≤ c₀)
    (hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ ell k K (C + r • B)) :
    ∀ D : DivisorA k K, defect k K D ≤ c₀ := by
  intro D
  let Dpos := D ⊔ (0 : DivisorA k K)
  have hDle : D ≤ Dpos := le_sup_left (a := D) (b := 0)
  have hDposeff : IsEffective k K Dpos := fun v => le_max_right (D v) 0
  obtain ⟨r, hr⟩ := hgrow (deg k K Dpos + 1)
  let Dr := C + r • B
  have hsub := ell_sub_effective_sub_ge (k := k) (K := K) (D := Dr - Dpos) (E := Dpos) hDposeff
  rw [sub_add_cancel] at hsub
  have hellpos : 0 < ell k K (Dr - Dpos) := by
    linarith
  obtain ⟨f, hfne⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)).1 hellpos
  let fK : K := f.val
  have hfKne : fK ≠ 0 := fun h => hfne (Subtype.ext h)
  have hmem : memRRspace k K (Dr - Dpos) fK := f.property
  have hDposle : Dpos ≤ Dr + principalDivisorA k K (Additive.ofMul (Units.mk0 fK hfKne)) :=
    le_add_principal_of_memRRspace (k := k) (K := K) hfKne hmem
  have hDle' : D ≤ Dr + principalDivisorA k K (Additive.ofMul (Units.mk0 fK hfKne)) :=
    le_trans hDle hDposle
  calc
    defect k K D ≤
        defect k K (Dr + principalDivisorA k K (Additive.ofMul (Units.mk0 fK hfKne))) :=
      defect_mono' (k := k) (K := K) hDle'
    _ = defect k K Dr := defect_add_principal (k := k) (K := K) Dr _
    _ ≤ c₀ := hmono r
end RiemannFamily
theorem defect_le_chart_family (D : DivisorA k K) :
    defect k K D ≤
      deg k K (basisPoleBound k K (Module.finBasis k⟮X⟯ K)) + 1 -
        Module.finrank k⟮X⟯ K := by
  let b := Module.finBasis k⟮X⟯ K
  let n := Module.finrank k⟮X⟯ K
  let C := basisPoleBound k K b
  let B := polarDivisor k K (XK k K)
  let c₀ := deg k K C + 1 - n
  have hmono : ∀ r : ℕ, defect k K (C + r • B) ≤ c₀ := by
    intro r
    have hdeg : deg k K (C + r • B) = deg k K C + (r : ℤ) * deg k K B := by
      rw [add_comm, ← nsmul_eq_mul, deg_add, deg_nsmul, nsmul_eq_mul, add_comm]
    have hell := ell_family_ge (k := k) (K := K) (n := n) (r := r) b
    have hBdeg : deg k K B = (n : ℤ) := deg_polarX_eq_finrank (k := k) (K := K)
    have hcast : (n * (r + 1) : ℤ) ≤ ell k K (C + r • B) := Nat.cast_le.mpr hell
    dsimp only [defect]
    rw [hdeg, hBdeg]
    linarith
  have hn : 0 < n := Module.finrank_pos
  have hgrow : ∀ m : ℤ, ∃ r : ℕ, m ≤ ell k K (C + r • B) := by
    intro m
    by_cases hm : m ≤ 0
    · refine ⟨0, ?_⟩
      have h0le : (0 : DivisorA k K) ≤ C + 0 • B := fun v =>
        show 0 ≤ (C + 0 • B) v by
          simpa [Finsupp.add_apply, Finsupp.nsmul_apply] using
            basisPoleBound_nonneg (k := k) (K := K) b v
      have hmono0 : (ell k K (0 : DivisorA k K) : ℤ) ≤ ell k K (C + 0 • B) := by
        exact_mod_cast Submodule.finrank_mono (RRspace_mono (k := k) (K := K) h0le)
      rw [ell_zero (k := k) (K := K)] at hmono0
      linarith
    · have hmpos : 0 < m := by omega
      let mnat := Int.toNat m
      have hmNat : (mnat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
      refine ⟨mnat, ?_⟩
      have hge := ell_family_ge (k := k) (K := K) (n := n) (r := mnat) b
      have hcast : (n * (mnat + 1) : ℤ) ≤ ell k K (C + mnat • B) := Nat.cast_le.mpr hge
      have hbound : m ≤ (n * (mnat + 1) : ℤ) := by
        rw [← hmNat]
        have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
        nlinarith [show (0 : ℤ) < m from hmpos]
      linarith
  exact defect_le_of_family (k := k) (K := K) B C c₀ hmono hgrow D
theorem exists_max_defect :
    ∃ g : ℕ, (∀ D : DivisorA k K, defect k K D ≤ (g : ℤ)) ∧
      ∃ D : DivisorA k K, defect k K D = (g : ℤ) := by
  let b := Module.finBasis k⟮X⟯ K
  let n := Module.finrank k⟮X⟯ K
  let C := basisPoleBound k K b
  let c₀ := deg k K C + 1 - n
  have hbound : ∀ D : DivisorA k K, defect k K D ≤ c₀ :=
    fun D => defect_le_chart_family (k := k) (K := K) D
  have hzero : defect k K (0 : DivisorA k K) = 0 := by
    dsimp only [defect]
    rw [deg_zero (k := k) (K := K), ell_zero (k := k) (K := K)]
    omega
  have hInh : ∃ z : ℤ, ∃ D : DivisorA k K, defect k K D = z := ⟨0, 0, hzero⟩
  have hBdd : ∃ b : ℤ, ∀ z : ℤ, (∃ D : DivisorA k K, defect k K D = z) → z ≤ b := by
    refine ⟨c₀, ?_⟩
    intro z ⟨D, hD⟩
    simpa [hD] using hbound D
  obtain ⟨g', hg', hgmax⟩ := Int.exists_greatest_of_bdd hBdd hInh
  have hg'nn : 0 ≤ g' := hgmax 0 ⟨0, hzero⟩
  refine ⟨g'.toNat, ?_, ?_⟩
  · intro D
    have hle := hgmax (defect k K D) ⟨D, rfl⟩
    calc defect k K D ≤ g' := hle
      _ = (g'.toNat : ℤ) := (Int.toNat_of_nonneg hg'nn).symm
  · obtain ⟨D, hD⟩ := hg'
    refine ⟨D, ?_⟩
    rw [Int.toNat_of_nonneg hg'nn]
    exact hD
noncomputable def genus : ℕ :=
  Classical.choose (exists_max_defect k K)
theorem riemann_ineq (D : DivisorA k K) :
    (ell k K D : ℤ) ≥ deg k K D + 1 - (genus k K : ℤ) := by
  have h := (Classical.choose_spec (exists_max_defect k K)).1 D
  simp only [defect, genus] at h ⊢
  omega
theorem defect_le (D : DivisorA k K) : defect k K D ≤ genus k K := by
  have h := riemann_ineq k K D
  simp only [defect]
  omega
theorem exists_defect_eq : ∃ D : DivisorA k K, defect k K D = genus k K := by
  simpa only [genus] using (Classical.choose_spec (exists_max_defect k K)).2
noncomputable def indexOfSpecialty (D : DivisorA k K) : ℕ :=
  (ell k K D - (deg k K D + 1 - (genus k K : ℤ))).toNat
theorem indexOfSpecialty_eq (D : DivisorA k K) :
    (indexOfSpecialty k K D : ℤ) = ell k K D - (deg k K D + 1 - (genus k K : ℤ)) := by
  have h := riemann_ineq k K D
  rw [indexOfSpecialty, Int.toNat_of_nonneg]
  omega
noncomputable def finrankAdeleQuotient (D : DivisorA k K) : ℕ :=
  Module.finrank k <|
    (AdeleSpace k K) ⧸ (adeleFilt k K D + diagonalSubmodule k K)
section PolarDivisor
end PolarDivisor
section RatFunc
end RatFunc
end FunctionField.Chart
end
end
end


