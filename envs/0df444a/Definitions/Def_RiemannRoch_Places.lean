-- Prove2me | Definitions.Def_RiemannRoch_Places
-- name    : RiemannRoch_Places
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:27:20.474345+00:00
-- url     : https://prove2.me/theorems/876802d1-c91c-4e96-b255-b313b8189fca
-- title:
--   Places of a function field: valuation-ring places and the two-chart presentation
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$.
--
--   This file introduces the places of $K/k$ in two presentations.
--
--   1. **Intrinsic places.** A place of $K/k$ is a valuation subring $\mathcal O_P\subsetneq K$ containing $k$ whose value group is order-isomorphic to $\mathbb Z$. It carries its normalized discrete valuation $v_P$, its residue field $k_P=\mathcal O_P/\mathfrak m_P$ (a $k$-algebra) and its degree $\deg P=\dim_k k_P$.
--   2. **The valuation ring at infinity.** $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$, where $\deg f$ is the degree of the numerator minus that of the denominator, with maximal ideal $\mathfrak m_\infty$; it is a Dedekind domain (a discrete valuation ring) and its residue field is identified with $k$: $k\xrightarrow{\ \sim\ }\mathcal O_\infty/\mathfrak m_\infty$, so $\dim_k\mathcal O_\infty/\mathfrak m_\infty=1$.
--   3. **The two charts.** Let $\mathcal O_K$ be the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ the integral closure of $\mathcal O_\infty$ in $K$; both are Dedekind domains with fraction field $K$, finite over $k[X]$, resp. $\mathcal O_\infty$, and $k$-algebras. The *chart places* are
--   $$\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\ \sqcup\ \operatorname{Spec}^1(\mathcal O_{K,\infty})$$
--   (finite places, then infinite places), each with its $\mathfrak p$-adic valuation; the residue fields $\mathcal O_K/P$ and $\mathcal O_{K,\infty}/P$ are finite-dimensional over $k$, and $\dim_k\mathcal O_K/P$ is the degree of a finite chart place.
--   4. **Chart divisors.** A chart divisor is a finitely supported function $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$, and the chart principal divisor of $x\in K^\times$ collects the principal divisors of $x$ in $\mathcal O_K$ and in $\mathcal O_{K,\infty}$.
--
--   The file also contains the structural lemmas these definitions need: the $\mathfrak p$-adic valuation of $x\in L^\times$ in a Dedekind domain is $\exp(-v_{\mathfrak p}(xR))$, so that the valuation of $x$ at a chart place is read off from the coefficient of the place in $\operatorname{div}(x)$; every $z\in k(X)$ with $\deg z\le0$ differs from a constant by $0$ or by an element of negative degree; the value group $\mathbb Z\cup\{0\}$ has no nontrivial order automorphism, so that the normalization of an intrinsic place is unique; and nonzero constants have valuation at most one at every chart place.
--
--   The chart presentation makes places computable through Dedekind domains, while the intrinsic presentation is the one used in the final, coordinate-free statements. In the chain of definition files it imports `RiemannRoch_Divisors` and is imported by `RiemannRoch_FunctionFieldDivisor1`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. Intrinsic places are `FunctionField.Place k K` (only `Algebra k K` is needed); chart places are the sum type `FunctionField.Chart.PlaceA k K`, chart divisors are `FunctionField.Chart.DivisorA k K := PlaceA k K →₀ ℤ` and the chart principal divisor is `principalDivisorA`. $\mathcal O_\infty$ is `inftyValuationSubring k`, the valuation subring of Mathlib's `RatFunc.inftyValuation`, $\mathcal O_K$ is Mathlib's `FunctionField.ringOfIntegers k K` and $\mathcal O_{K,\infty}$ is `infiniteIntegers k K`. The discreteness of an intrinsic place is stored as the existence of an order isomorphism between its value group and $\mathbb Z_{m0}$; since $\mathbb Z_{m0}$ has no nontrivial order automorphism (proved here), the normalized valuation does not depend on that choice. Valuations take values in $\mathbb Z_{m0}=\{0\}\cup\{\exp(n):n\in\mathbb Z\}$, written multiplicatively, so that the Lean valuation of $f\ne0$ at $P$ is $\exp(-v_P(f))$; the inequality $\exp(-v_P(f))\le\exp(D(P))$ is the additive condition $v_P(f)\ge -D(P)$.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.1 (valuation rings, places, normalized discrete valuations, residue class field and degree of a place), Section 1.2 (the infinite place of the rational function field) and Section 1.4 (principal divisors); the two-chart description via integral closures of $k[x]$ and of the valuation ring at infinity corresponds to the holomorphy rings of Section 3.2 (cf.). Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Place.lean

import Mathlib
import Definitions.Def_RiemannRoch_Divisors

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
open scoped nonZeroDivisors Polynomial RatFunc WithZero
noncomputable section
namespace FractionalIdeal
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
theorem valuation_eq_exp_neg_count (v : IsDedekindDomain.HeightOneSpectrum R) (x : Kˣ) :
    v.valuation K (x : K) =
      WithZero.exp (-count K v (spanSingleton R⁰ (x : K))) := by
  let n : R := Classical.choose (IsLocalization.exists_mk'_eq R⁰ (x : K))
  let d : R⁰ := Classical.choose
    (Classical.choose_spec (IsLocalization.exists_mk'_eq R⁰ (x : K)))
  have hx : IsLocalization.mk' K n d = (x : K) :=
    Classical.choose_spec
      (Classical.choose_spec (IsLocalization.exists_mk'_eq R⁰ (x : K)))
  have hn : n ≠ 0 := by
    intro hn
    rw [hn, IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  have hI : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ (algebraMap R K (d : R))⁻¹ *
        (Ideal.span {n} : Ideal R) := by
    rw [← hx, IsFractionRing.mk'_eq_div, div_eq_mul_inv,
      coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, mul_comm]
  conv_lhs =>
    rw [← hx, v.valuation_of_mk', v.intValuation_if_neg hn,
      v.intValuation_if_neg (nonZeroDivisors.ne_zero d.property)]
  rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hI,
    ← WithZero.exp_sub]
  congr 1
  ring
end FractionalIdeal
namespace RatFunc
variable {k : Type*} [Field k]
theorem exists_sub_C_intDegree_neg (z : k⟮X⟯) (hzdeg : z.intDegree ≤ 0) :
    ∃ c : k, z - C c = 0 ∨ (z - C c).intDegree < 0 := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  by_cases hneg : z.intDegree < 0
  · exact ⟨0, Or.inr (by simpa using hneg)⟩
  have hzdeg0 : z.intDegree = 0 := by omega
  let c : k := z.num.leadingCoeff / z.denom.leadingCoeff
  let p : k[X] := z.num - Polynomial.C c * z.denom
  have hrepr : z - C c =
      algebraMap k[X] k⟮X⟯ p / algebraMap k[X] k⟮X⟯ z.denom := by
    conv_lhs => lhs; rw [← z.num_div_denom]
    rw [← RatFunc.algebraMap_C]
    simp only [p, map_sub, map_mul]
    apply (eq_div_iff (RatFunc.algebraMap_ne_zero z.denom_ne_zero)).2
    rw [sub_mul, div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero z.denom_ne_zero)]
  by_cases hp : p = 0
  · exact ⟨c, Or.inl (by rw [hrepr, hp, map_zero, zero_div])⟩
  refine ⟨c, Or.inr ?_⟩
  have hnumdeg : z.num.natDegree = z.denom.natDegree := by
    simp only [RatFunc.intDegree] at hzdeg0
    omega
  have hnum0 : z.num ≠ 0 := RatFunc.num_ne_zero hz
  have hden0 : z.denom ≠ 0 := z.denom_ne_zero
  have hlcnum : z.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hnum0
  have hlcden : z.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hden0
  have hc : c ≠ 0 := div_ne_zero hlcnum hlcden
  have hCmul0 : Polynomial.C c * z.denom ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) hden0
  have hdegree : z.num.degree = (Polynomial.C c * z.denom).degree := by
    rw [Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_mul,
      Polynomial.degree_C hc, zero_add, Polynomial.degree_eq_natDegree hden0, hnumdeg]
  have hlc : z.num.leadingCoeff =
      (Polynomial.C c * z.denom).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    dsimp only [c]
    field_simp
  have hpdeg : p.degree < z.num.degree := by
    simpa only [p] using Polynomial.degree_sub_lt hdegree hnum0 hlc
  have hpnat : p.natDegree < z.denom.natDegree := by
    rw [Polynomial.natDegree_lt_iff_degree_lt hp]
    rw [← hnumdeg]
    simpa [Polynomial.degree_eq_natDegree hnum0] using hpdeg
  rw [hrepr, RatFunc.intDegree_div]
  · simp only [RatFunc.intDegree_polynomial]
    omega
  · exact RatFunc.algebraMap_ne_zero hp
  · exact RatFunc.algebraMap_ne_zero hden0
end RatFunc
namespace FunctionField
variable (k K : Type*) [Field k] [Field K]
open MonoidWithZeroHom
 noncomputable def withZeroMulIntLogAddEquiv
    (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) : ℤ ≃+ ℤ := by
  let f : ℤ →+ ℤ :=
    { toFun := fun z => WithZero.log (e (WithZero.exp z))
      map_zero' := by simp
      map_add' := by
        intro x y
        rw [WithZero.exp_add, map_mul]
        rw [WithZero.log_mul]
        · simp
        · simp }
  refine AddEquiv.ofBijective f ?_
  constructor
  · intro x y h
    apply WithZero.exp_injective
    apply e.injective
    simpa [f] using congrArg WithZero.exp h
  · intro y
    refine ⟨WithZero.log (e.symm (WithZero.exp y)), ?_⟩
    dsimp [f]
    rw [WithZero.exp_log]
    · simp
    · simp
theorem orderMonoidIso_withZeroMulInt_eq_refl (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) :
    e = OrderMonoidIso.refl ℤᵐ⁰ := by
  have hmono : Monotone (withZeroMulIntLogAddEquiv e) := by
    intro x y hxy
    dsimp [withZeroMulIntLogAddEquiv]
    change WithZero.log (e (WithZero.exp x)) ≤
      WithZero.log (e (WithZero.exp y))
    apply WithZero.exp_le_exp.mp
    rw [WithZero.exp_log, WithZero.exp_log]
    · exact e.toOrderIso.monotone (WithZero.exp_le_exp.mpr hxy)
    · simp
    · simp
  rcases Int.addEquiv_eq_refl_or_neg (withZeroMulIntLogAddEquiv e) with h | h
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [← WithZero.exp_log hx]
      have h2 : WithZero.log (e (WithZero.exp (WithZero.log x))) = WithZero.log x :=
        DFunLike.congr_fun h (WithZero.log x)
      have hne : e (WithZero.exp (WithZero.log x)) ≠ 0 := by simp
      rw [← WithZero.exp_log hne, h2]
      rfl
  · have hle := hmono (show (0 : ℤ) ≤ 1 by omega)
    rw [h] at hle
    norm_num at hle
theorem orderMonoidIso_withZeroMulInt_unique {G : Type*}
    [LinearOrderedCommGroupWithZero G] (e f : G ≃*o ℤᵐ⁰) : e = f := by
  have h := orderMonoidIso_withZeroMulInt_eq_refl (e.symm.trans f)
  ext x
  have hx := DFunLike.congr_fun h (e x)
  simpa using hx.symm
structure Place [Algebra k K] where
  toValuationSubring : ValuationSubring K
  ne_top : toValuationSubring ≠ ⊤
  triv_on_k : ∀ c : k, algebraMap k K c ∈ toValuationSubring
  isDiscrete : Nonempty
    (ValueGroup₀ (.ofClass toValuationSubring.valuation) ≃*o ℤᵐ⁰)
namespace Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
@[ext]
theorem ext {v w : Place k K}
    (h : v.toValuationSubring = w.toValuationSubring) : v = w := by
  cases v
  cases w
  cases h
  rfl
instance : SetLike (Place k K) K where
  coe v := v.toValuationSubring
  coe_injective := by
    intro v w h
    exact ext (SetLike.coe_injective h)
noncomputable def normalization (v : Place k K) :
    ValueGroup₀ (.ofClass v.toValuationSubring.valuation) ≃*o ℤᵐ⁰ :=
  Classical.choice v.isDiscrete
noncomputable def valuation (v : Place k K) : Valuation K ℤᵐ⁰ :=
  v.toValuationSubring.valuation.restrict.map
    v.normalization.toMonoidWithZeroHom v.normalization.toOrderIso.monotone
theorem valuation_isEquiv_canonical (v : Place k K) :
    v.valuation.IsEquiv v.toValuationSubring.valuation := by
  exact (Valuation.isEquiv_map_self_of_strictMono
    v.normalization.toMonoidWithZeroHom v.normalization.strictMono).trans
      v.toValuationSubring.valuation.isEquiv_restrict.symm
@[simp]
theorem valuationSubring_valuation (v : Place k K) :
    v.valuation.valuationSubring = v.toValuationSubring := by
  exact (Valuation.isEquiv_iff_valuationSubring _ _).mp
    v.valuation_isEquiv_canonical |>.trans
      v.toValuationSubring.valuationSubring_valuation
instance valuation_isTrivialOn (v : Place k K) : v.valuation.IsTrivialOn k where
  eq_one c hc := by
    let w := v.toValuationSubring.valuation
    have hc_le : w (algebraMap k K c) ≤ 1 := by
      rw [v.toValuationSubring.valuation_le_one_iff]
      exact v.triv_on_k c
    have hc_inv_le : w (algebraMap k K c⁻¹) ≤ 1 := by
      rw [v.toValuationSubring.valuation_le_one_iff]
      exact v.triv_on_k c⁻¹
    have hmap_ne : w (algebraMap k K c) ≠ 0 := by simp [hc]
    have hmap_pos : 0 < w (algebraMap k K c) := zero_lt_iff.mpr hmap_ne
    have hinv_le : (w (algebraMap k K c))⁻¹ ≤ 1 := by
      simpa only [map_inv₀, map_inv] using hc_inv_le
    have hw : w (algebraMap k K c) = 1 :=
      le_antisymm hc_le ((inv_le_one₀ hmap_pos).1 hinv_le)
    exact v.valuation_isEquiv_canonical.eq_one_iff_eq_one.mpr hw
instance valuation_isNontrivial (v : Place k K) : v.valuation.IsNontrivial := by
  have hcanonical : v.toValuationSubring.valuation.IsNontrivial := by
    by_contra h
    exact v.ne_top (v.toValuationSubring.eq_top_iff.mpr h)
  exact Valuation.isNontrivial_of_isEquiv
    v.valuation_isEquiv_canonical.symm hcanonical
instance algebraValuationSubring (v : Place k K) : Algebra k v.toValuationSubring :=
  (algebraMap k K).codRestrict v.toValuationSubring (fun c ↦ v.triv_on_k c) |>.toAlgebra
abbrev residueField (v : Place k K) :=
  IsLocalRing.ResidueField v.toValuationSubring
noncomputable def degree (v : Place k K) : ℕ :=
  Module.finrank k v.residueField
end Place
namespace Chart
local instance instDecidableEqRatFuncRiemannRoch : DecidableEq k⟮X⟯ := Classical.decEq _
abbrev inftyValuationSubring := (RatFunc.inftyValuation k).valuationSubring
namespace inftyValuationSubring
instance : IsDedekindDomain (inftyValuationSubring k) := by infer_instance
instance : Algebra k (inftyValuationSubring k) :=
  (RatFunc.C.codRestrict (inftyValuationSubring k) fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (RatFunc.inftyValuation.C k hc).le).toAlgebra
local notation "ᵐ∞" => IsLocalRing.maximalIdeal (inftyValuationSubring k)
local instance : Field (inftyValuationSubring k ⧸ ᵐ∞) := Ideal.Quotient.field ᵐ∞
theorem residue_algebraMap_surjective :
    Function.Surjective (algebraMap k (inftyValuationSubring k ⧸ ᵐ∞)) := by
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  let z : k⟮X⟯ := (a : k⟮X⟯)
  have hzdeg : z.intDegree ≤ 0 := by
    by_cases hz : z = 0
    · simp [hz]
    have ha := a.property
    rw [Valuation.mem_valuationSubring_iff] at ha
    change RatFunc.inftyValuation k z ≤ 1 at ha
    have hv : RatFunc.inftyValuation k z = WithZero.exp z.intDegree :=
      RatFunc.inftyValuation_of_nonzero k hz
    rw [hv] at ha
    exact WithZero.exp_le_exp.mp (by simpa only [WithZero.exp_zero] using ha)
  obtain ⟨c, hc | hc⟩ := RatFunc.exists_sub_C_intDegree_neg z hzdeg
  · refine ⟨c, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hzero : algebraMap k (inftyValuationSubring k) c - a = 0 := by
      apply Subtype.ext
      change RatFunc.C c - z = 0
      rw [show RatFunc.C c - z = -(z - RatFunc.C c) by ring, hc, neg_zero]
    rw [hzero]
    exact ᵐ∞.zero_mem
  · refine ⟨c, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
    have hne : z - RatFunc.C c ≠ 0 := by
      intro h
      rw [h, RatFunc.intDegree_zero] at hc
      omega
    have hpos : a - algebraMap k (inftyValuationSubring k) c ∈ ᵐ∞ := by
      rw [Valuation.mem_maximalIdeal_iff]
      change RatFunc.inftyValuation k (z - RatFunc.C c) < 1
      have hv : RatFunc.inftyValuation k (z - RatFunc.C c) =
          WithZero.exp (z - RatFunc.C c).intDegree :=
        RatFunc.inftyValuation_of_nonzero k hne
      rw [hv]
      exact WithZero.exp_lt_exp.mpr hc
    simpa only [neg_sub] using ᵐ∞.neg_mem hpos
noncomputable def residueAlgEquiv :
    k ≃ₐ[k] (inftyValuationSubring k ⧸ ᵐ∞) :=
  AlgEquiv.ofBijective (Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞))
    ⟨(Algebra.ofId k (inftyValuationSubring k ⧸ ᵐ∞)).injective,
      residue_algebraMap_surjective k⟩
instance finiteDimensionalResidueField :
    FiniteDimensional k (inftyValuationSubring k ⧸ ᵐ∞) :=
  (residueAlgEquiv k).toLinearEquiv.finiteDimensional
@[simp]
theorem finrank_residueField :
    Module.finrank k (inftyValuationSubring k ⧸ ᵐ∞) = 1 := by
  rw [← (residueAlgEquiv k).toLinearEquiv.finrank_eq]
  exact Module.finrank_self k
end inftyValuationSubring
variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
abbrev infiniteIntegers := integralClosure (inftyValuationSubring k) K
namespace infiniteIntegers
instance isTorsionFreeOverInfinityRing :
    Module.IsTorsionFree (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.isTorsionFree (inftyValuationSubring k) K
instance : IsFractionRing (infiniteIntegers k K) K :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)
instance : IsDedekindDomain (infiniteIntegers k K) :=
  integralClosure.isDedekindDomain (inftyValuationSubring k) k⟮X⟯ K
instance : Module.Finite (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsIntegralClosure.finite (inftyValuationSubring k) k⟮X⟯ K (infiniteIntegers k K)
instance : Algebra k (infiniteIntegers k K) :=
  ((algebraMap (inftyValuationSubring k) (infiniteIntegers k K)).comp
    (algebraMap k (inftyValuationSubring k))).toAlgebra
instance : IsScalarTower k (inftyValuationSubring k) (infiniteIntegers k K) :=
  IsScalarTower.of_algebraMap_eq (R := k) (S := inftyValuationSubring k)
    (A := infiniteIntegers k K) fun _ => rfl
end infiniteIntegers
namespace ringOfIntegers
instance isTorsionFreeOverPolynomial :
    Module.IsTorsionFree k[X] (ringOfIntegers k K) := by
  letI : FaithfulSMul k[X] K :=
    (faithfulSMul_iff_algebraMap_injective k[X] K).2
      (FunctionField.algebraMap_injective k K)
  exact IsIntegralClosure.isTorsionFree k[X] K
instance algebraOverConstants : Algebra k (ringOfIntegers k K) :=
  ((algebraMap k[X] (ringOfIntegers k K)).comp (algebraMap k k[X])).toAlgebra
instance isScalarTowerConstants : IsScalarTower k k[X] (ringOfIntegers k K) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
instance finiteTypeOverConstants : Algebra.FiniteType k (ringOfIntegers k K) :=
  Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
instance moduleFiniteOverPolynomial : Module.Finite k[X] (ringOfIntegers k K) :=
  IsIntegralClosure.finite k[X] k⟮X⟯ K (ringOfIntegers k K)
end ringOfIntegers
abbrev PlaceA :=
  IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K) ⊕
    IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)
def placeValuation : PlaceA k K → Valuation K ℤᵐ⁰
  | Sum.inl v => v.valuation K
  | Sum.inr v => v.valuation K
abbrev DivisorA := PlaceA k K →₀ ℤ
namespace PlaceA
instance finiteDimensionalResidueFieldFinite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    FiniteDimensional k (ringOfIntegers k K ⧸ v.asIdeal) := by
  letI : Field (ringOfIntegers k K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact finite_of_finite_type_of_isJacobsonRing k _
instance finiteDimensionalResidueFieldInfinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    FiniteDimensional k (infiniteIntegers k K ⧸ v.asIdeal) := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p : Ideal A := v.asIdeal.under A
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : p.IsMaximal := Ideal.IsMaximal.under A v.asIdeal
  letI : v.asIdeal.LiesOver p := ⟨rfl⟩
  letI : Field (A ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Algebra (A ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  have hp : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  letI : FiniteDimensional k (A ⧸ p) := by
    rw [hp]
    exact inftyValuationSubring.finiteDimensionalResidueField k
  letI : FiniteDimensional (A ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg'_pos p v.asIdeal
    rw [Ideal.inertiaDeg'_algebraMap] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  letI : IsScalarTower k (A ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact FiniteDimensional.trans k (A ⧸ p) (S ⧸ v.asIdeal)
noncomputable def finiteDegree
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) : ℕ :=
  Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal)
end PlaceA
noncomputable def principalDivisorA : Additive Kˣ →+ DivisorA k K :=
  (Finsupp.mapDomain.addMonoidHom Sum.inl).comp
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K)) +
    (Finsupp.mapDomain.addMonoidHom Sum.inr).comp
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K))
@[simp]
theorem principalDivisorA_apply_finite (x : Additive Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    principalDivisorA k K x (Sum.inl v) =
      FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K) x v := by
  simp only [principalDivisorA, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  change Finsupp.mapDomain Sum.inl
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K) x) (Sum.inl v) +
    Finsupp.mapDomain Sum.inr
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K) x)
        (Sum.inl v) = _
  rw [Finsupp.mapDomain_apply Sum.inl_injective]
  rw [Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨w, h⟩
    cases h
@[simp]
theorem principalDivisorA_apply_infinite (x : Additive Kˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    principalDivisorA k K x (Sum.inr v) =
      FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K) x v := by
  simp only [principalDivisorA, AddMonoidHom.add_apply, AddMonoidHom.coe_comp,
    Function.comp_apply]
  change Finsupp.mapDomain Sum.inl
      (FractionalIdeal.principalDivisor (R := ringOfIntegers k K) (K := K) x) (Sum.inr v) +
    Finsupp.mapDomain Sum.inr
      (FractionalIdeal.principalDivisor (R := infiniteIntegers k K) (K := K) x)
        (Sum.inr v) = _
  rw [Finsupp.mapDomain_apply Sum.inr_injective]
  rw [Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨w, h⟩
    cases h
theorem placeValuation_eq_exp_neg_principalDivisor (x : Additive Kˣ) (v : PlaceA k K) :
    placeValuation k K v (x.toMul : K) =
      WithZero.exp (-(principalDivisorA k K x v)) := by
  rcases v with v | v
  · rw [principalDivisorA_apply_finite, FractionalIdeal.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul
  · rw [principalDivisorA_apply_infinite, FractionalIdeal.principalDivisor_apply]
    exact FractionalIdeal.valuation_eq_exp_neg_count v x.toMul
section ConstantField
variable [Algebra k K] [IsScalarTower k k[X] K]
instance ringOfIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (ringOfIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] (ringOfIntegers k K) K,
      ← IsScalarTower.algebraMap_apply k k[X] (ringOfIntegers k K)]
instance infiniteIntegers.isScalarTowerConstantsFractions :
    IsScalarTower k (infiniteIntegers k K) K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    have h₁ : algebraMap k (infiniteIntegers k K) c =
        algebraMap (inftyValuationSubring k) (infiniteIntegers k K)
          (algebraMap k (inftyValuationSubring k) c) := rfl
    have h₂ : algebraMap (inftyValuationSubring k) k⟮X⟯
        (algebraMap k (inftyValuationSubring k) c) = RatFunc.C c := rfl
    rw [h₁, ← IsScalarTower.algebraMap_apply (inftyValuationSubring k) (infiniteIntegers k K) K,
      IsScalarTower.algebraMap_apply (inftyValuationSubring k) k⟮X⟯ K, h₂,
      IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, Polynomial.algebraMap_eq,
      RatFunc.algebraMap_C]
theorem placeValuation_algebraMap_le_one (v : PlaceA k K) (c : k) :
    placeValuation k K v (algebraMap k K c) ≤ 1 := by
  obtain w | w := v
  · show w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K]
    exact w.valuation_le_one _
  · show w.valuation K (algebraMap k K c) ≤ 1
    rw [IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K]
    exact w.valuation_le_one _
end ConstantField
end Chart
end FunctionField
end
end
end


