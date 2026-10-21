-- Prove2me | Definitions.Def_RiemannRoch_Divisors
-- name    : RiemannRoch_Divisors
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:25:28.859698+00:00
-- url     : https://prove2.me/theorems/a7c697f0-0a89-4261-b193-27da1eb08a03
-- title:
--   Divisors of a Dedekind domain and relative norms of primes in separable extensions
-- statement:
--   Let $R$ be a Dedekind domain with fraction field $L$, and write $\operatorname{Spec}^1(R)$ for its set of height-one (that is, nonzero) prime ideals $\mathfrak p$.
--
--   This file introduces the divisor theory of Dedekind domains on which the whole formalization rests:
--
--   1. **Divisors.** $\operatorname{Div}(R)=\bigoplus_{\mathfrak p\in\operatorname{Spec}^1(R)}\mathbb Z\,\mathfrak p$, the group of finitely supported functions $\operatorname{Spec}^1(R)\to\mathbb Z$.
--   2. **Divisor of a fractional ideal.** A nonzero fractional ideal $I$ of $R$ in $L$ has divisor $\operatorname{div}(I)=\sum_{\mathfrak p}v_{\mathfrak p}(I)\,\mathfrak p$, where $v_{\mathfrak p}(I)$ is the exponent of $\mathfrak p$ in the factorization of $I$; conversely a divisor $\sum n_{\mathfrak p}\mathfrak p$ gives the fractional ideal $\prod_{\mathfrak p}\mathfrak p^{n_{\mathfrak p}}$. The two constructions are inverse to each other and give a group isomorphism
--   $$\{\text{nonzero fractional ideals of }R\}\ \xrightarrow{\ \sim\ }\ \operatorname{Div}(R),\qquad I\longmapsto\operatorname{div}(I).$$
--   3. **Principal divisors.** The homomorphism $L^\times\to\operatorname{Div}(R)$, $x\mapsto\operatorname{div}(x)=\operatorname{div}(xR)$.
--   4. **Weighted degrees.** For a weight $w$ assigning a natural number to every ideal of $R$, the homomorphism $\operatorname{Div}(R)\to\mathbb Z$, $\sum n_{\mathfrak p}\mathfrak p\mapsto\sum n_{\mathfrak p}\,w(\mathfrak p)$.
--
--   The file also contains the structural lemmas these definitions need: the weighted degree of the divisor of a nonzero integral ideal $J$ is the sum of $w$ over the prime factors of $J$ counted with multiplicity, hence for $x=n/d$ ($n\in R$, $d\in R\setminus\{0\}$) the weighted degree of $\operatorname{div}(x)$ is the sum for $(n)$ minus the sum for $(d)$. It also proves, for a finite, torsion-free extension $S/R$ of Dedekind domains whose fraction-field extension is separable, that the relative norm of a maximal ideal $\mathfrak P$ of $S$ lying over the maximal ideal $\mathfrak p$ of $R$ is
--   $$N_{S/R}(\mathfrak P)=\mathfrak p^{\,f(\mathfrak P|\mathfrak p)},$$
--   where $f(\mathfrak P|\mathfrak p)=[S/\mathfrak P:R/\mathfrak p]$ is the inertia degree; consequently, for a nonzero ideal $I$ of $S$ and any weight $w$ on ideals of $R$, the sum of $w$ over the prime factors of $N_{S/R}(I)$ equals the sum of $f(\mathfrak P|\mathfrak P\cap R)\,w(\mathfrak P\cap R)$ over the prime factors $\mathfrak P$ of $I$ (with multiplicities).
--
--   These results make it possible to compute degrees of divisors of a function field prime by prime, through norms down to $k[X]$ and to the valuation ring at infinity. This is the first file of the chain of definition files of the publication, each importing the previous one: `RiemannRoch_Divisors` → `RiemannRoch_Places` → `RiemannRoch_FunctionFieldDivisor1` → `RiemannRoch_FunctionFieldDivisor2` → `RiemannRoch_FunctionFieldDivisor3` → `RiemannRoch_FunctionFieldDivisor4` → `RiemannRoch_RRSpace` → `RiemannRoch_Adeles` → `RiemannRoch_IntrinsicAdeles` → `RiemannRoch_GenusCharts` → `RiemannRoch_FilterChain1` → `RiemannRoch_FilterChain2` → `RiemannRoch_FilterChain3` → `RiemannRoch_FilterChain4` → `RiemannRoch_WeilDifferentials` → `RiemannRoch_WeierstrassDedekind` → `RiemannRoch_WeierstrassInfinity` → `RiemannRoch_WeierstrassGenus` → `WeilConjectures_RiemannRochFLT`.
--
--   **Formalization Note** The fraction field $L$ is the Lean variable `K` (with `[IsFractionRing R K]`). `IsDedekindDomain.Divisor R` is `HeightOneSpectrum R →₀ ℤ`; the coefficient $v_{\mathfrak p}(I)$ is Mathlib's `FractionalIdeal.count K v I`; the isomorphism is `FractionalIdeal.divisorEquiv : Additive (FractionalIdeal R⁰ K)ˣ ≃+ Divisor R`, principal divisors are `FractionalIdeal.principalDivisor : Additive Kˣ →+ Divisor R` and weighted degrees are `FractionalIdeal.weightedDegree w`. Prime factors with multiplicity are `UniqueFactorizationMonoid.normalizedFactors` and the inertia degree is Mathlib's `Ideal.inertiaDeg'`. The relative-norm identity `Ideal.relNorm_eq_pow_of_isMaximal_of_isSeparable` is a variant of Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`, which assumes instead that the fraction field of $R$ is perfect; its separability hypothesis is stated for `FractionRing S` over `FractionRing R`, and `Module.Finite R S` and `IsTorsionFree R S` are assumed.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4 (divisors and principal divisors of a function field) and Section 3.1 (inertia degree, cf.); the divisor theory of a general Dedekind domain and the relative-norm identity are standard commutative algebra used here as auxiliary lemmas of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Divisor.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/SeparableRelNorm.lean

import Mathlib

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
open IsDedekindDomain
open scoped nonZeroDivisors
namespace IsDedekindDomain
abbrev Divisor (R : Type*) [CommRing R] := HeightOneSpectrum R →₀ ℤ
end IsDedekindDomain
namespace FractionalIdeal
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
noncomputable def divisor (I : (FractionalIdeal R⁰ K)ˣ) : Divisor R :=
  Finsupp.mk (finite_factors (I : FractionalIdeal R⁰ K)).toFinset
    (fun v ↦ count K v I) fun _ ↦ (finite_factors (I : FractionalIdeal R⁰ K)).mem_toFinset
@[simp]
theorem divisor_apply (I : (FractionalIdeal R⁰ K)ˣ) (v : HeightOneSpectrum R) :
    divisor I v = count K v I := by
  classical
  simp [divisor]
noncomputable def ofDivisor (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (D : Divisor R) : (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (D.prod fun v n ↦ (v.asIdeal : FractionalIdeal R⁰ K) ^ n) <| by
    classical
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ ↦
      zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
@[simp]
theorem count_ofDivisor (D : Divisor R) (v : HeightOneSpectrum R) :
    count K v (ofDivisor K D : FractionalIdeal R⁰ K) = D v := by
  classical
  simpa [ofDivisor] using count_finsuppProd K v D
 theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v ↦ congr_arg ((v.asIdeal : FractionalIdeal R⁰ K) ^ ·) (h v)
noncomputable def divisorEquiv : Additive (FractionalIdeal R⁰ K)ˣ ≃+ Divisor R where
  toFun I := divisor I.toMul
  invFun D := Additive.ofMul (ofDivisor K D)
  left_inv I := by
    apply Additive.toMul.injective
    apply Units.ext
    change (ofDivisor K (divisor I.toMul) : FractionalIdeal R⁰ K) = I.toMul
    apply eq_of_count_eq (ofDivisor K (divisor I.toMul)).ne_zero I.toMul.ne_zero
    intro v
    rw [count_ofDivisor, divisor_apply]
  right_inv D := by
    ext v
    change count K v (ofDivisor K D : FractionalIdeal R⁰ K) = D v
    rw [count_ofDivisor]
  map_add' I J := by
    change divisor (I.toMul * J.toMul) = divisor I.toMul + divisor J.toMul
    ext v
    simp only [divisor_apply, Units.val_mul]
    exact count_mul K v I.toMul.ne_zero J.toMul.ne_zero
noncomputable def principalFractionalIdeal : Kˣ →* (FractionalIdeal R⁰ K)ˣ where
  toFun x := Units.mk0 (spanSingleton R⁰ (x : K)) (spanSingleton_ne_zero_iff.mpr x.ne_zero)
  map_one' := Units.ext spanSingleton_one
  map_mul' x y := Units.ext (spanSingleton_mul_spanSingleton (R := R) (x : K) y).symm
@[simp]
theorem principalFractionalIdeal_apply_coe (x : Kˣ) :
    (principalFractionalIdeal (R := R) (K := K) x : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ (x : K) := rfl
noncomputable def principalDivisor : Additive Kˣ →+ Divisor R :=
  divisorEquiv.toAddMonoidHom.comp principalFractionalIdeal.toAdditive
@[simp]
theorem principalDivisor_apply (x : Additive Kˣ) (v : HeightOneSpectrum R) :
    principalDivisor (R := R) (K := K) x v =
      count K v (spanSingleton R⁰ (x.toMul : K)) := by
  change divisor (principalFractionalIdeal x.toMul) v = _
  rw [divisor_apply, principalFractionalIdeal_apply_coe]
noncomputable def weightedDegree (w : Ideal R → ℕ) : Divisor R →+ ℤ where
  toFun D := D.sum fun v n => n * (w v.asIdeal : ℤ)
  map_zero' := by simp
  map_add' D E := by
    classical
    simp [Finsupp.sum_add_index, add_mul]
omit [IsDedekindDomain R] in
@[simp]
theorem weightedDegree_apply (w : Ideal R → ℕ) (D : Divisor R) :
    weightedDegree (R := R) w D =
      D.sum fun v n => n * (w v.asIdeal : ℤ) := rfl
theorem divisor_ideal_sum_eq_normalizedFactors_sum (J : Ideal R) (hJ : J ≠ ⊥)
    (w : Ideal R → ℕ) :
    let JU : (FractionalIdeal R⁰ K)ˣ :=
      Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)
    (divisor JU).sum (fun v n => n * (w v.asIdeal : ℤ)) =
      (((UniqueFactorizationMonoid.normalizedFactors J).map w).sum : ℤ) := by
  classical
  dsimp only
  rw [Finsupp.sum]
  let s := UniqueFactorizationMonoid.normalizedFactors J
  have hcoeff (v : HeightOneSpectrum R) :
      divisor (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)) v =
        (s.count v.asIdeal : ℤ) := by
    rw [divisor_apply, Units.val_mk0, count_coe K v hJ,
      Ideal.count_associates_factors_eq hJ v.isPrime v.ne_bot]
  have hsum :
      ∑ v ∈ (divisor
          (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ))).support,
          divisor (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)) v *
            (w v.asIdeal : ℤ) =
        ∑ P ∈ s.toFinset, (s.count P : ℤ) * (w P : ℤ) := by
    apply Finset.sum_bij (fun v _ => v.asIdeal)
    · intro v hv
      rw [Multiset.mem_toFinset, ← Multiset.count_ne_zero]
      intro hz
      have : divisor
          (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ)) v = 0 := by
        rw [hcoeff, hz, Nat.cast_zero]
      exact (Finsupp.mem_support_iff.mp hv) this
    · intro v₁ _ v₂ _ hv
      exact HeightOneSpectrum.ext hv
    · intro P hP
      rw [Multiset.mem_toFinset] at hP
      have hprime : Prime P :=
        UniqueFactorizationMonoid.prime_of_normalized_factor P hP
      let v : HeightOneSpectrum R :=
        ⟨P, Ideal.isPrime_of_prime hprime, hprime.ne_zero⟩
      refine ⟨v, ?_, rfl⟩
      rw [Finsupp.mem_support_iff, hcoeff]
      exact_mod_cast (Multiset.count_pos.mpr hP).ne'
    · intro v _
      rw [hcoeff]
  rw [hsum, Finset.sum_multiset_map_count]
  simp only [s, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul]
  push_cast
  rfl
theorem weightedDegree_divisor_ideal (J : Ideal R) (hJ : J ≠ ⊥)
    (w : Ideal R → ℕ) :
    weightedDegree (R := R) w
        (divisor (Units.mk0 (J : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.mpr hJ))) =
      (((UniqueFactorizationMonoid.normalizedFactors J).map w).sum : ℤ) :=
  divisor_ideal_sum_eq_normalizedFactors_sum J hJ w
theorem weightedDegree_principal_mk' (w : Ideal R → ℕ) (x : Kˣ) (n : R)
    (d : nonZeroDivisors R) (hnd : IsLocalization.mk' K n d = (x : K)) :
    weightedDegree (R := R) w (principalDivisor (Additive.ofMul x)) =
      (((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).map w).sum : ℤ) -
        (((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span {(d : R)})).map w).sum : ℤ) := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    exact x.ne_zero (by simpa [hn] using hnd.symm)
  have hd : (d : R) ≠ 0 := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero] using d.property
  have hspan : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ ((algebraMap R K) (d : R))⁻¹ *
        (Ideal.span {n} : FractionalIdeal R⁰ K) := by
    rw [← hnd, IsFractionRing.mk'_eq_div, coeIdeal_span_singleton,
      spanSingleton_mul_spanSingleton]
    congr 1
    simp only [div_eq_mul_inv]
    ac_rfl
  have hdiv : principalDivisor (R := R) (K := K) (Additive.ofMul x) =
      divisor (Units.mk0 (Ideal.span {n} : FractionalIdeal R⁰ K)
          (coeIdeal_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hn))) -
        divisor (Units.mk0 (Ideal.span {(d : R)} : FractionalIdeal R⁰ K)
          (coeIdeal_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hd))) := by
    ext v
    rw [principalDivisor_apply, Finsupp.sub_apply, divisor_apply, divisor_apply]
    change count K v (spanSingleton R⁰ (x : K)) =
      count K v (Ideal.span {n} : FractionalIdeal R⁰ K) -
        count K v (Ideal.span {(d : R)} : FractionalIdeal R⁰ K)
    rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hspan,
      count_coe K v (Ideal.span_singleton_eq_bot.not.mpr hn),
      count_coe K v (Ideal.span_singleton_eq_bot.not.mpr hd)]
  rw [hdiv, map_sub,
    weightedDegree_divisor_ideal (K := K) (Ideal.span {n})
      (Ideal.span_singleton_eq_bot.not.mpr hn) w,
    weightedDegree_divisor_ideal (K := K) (Ideal.span {(d : R)})
      (Ideal.span_singleton_eq_bot.not.mpr hd) w]
end FractionalIdeal
end
end

section
section
open Module
open UniqueFactorizationMonoid
open scoped nonZeroDivisors
namespace Ideal
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [IsTorsionFree R S]
theorem relNorm_eq_pow_of_isMaximal_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (P : Ideal S) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ p.inertiaDeg' P := by
  let K := FractionRing R
  let L := FractionRing S
  letI : Algebra K L := FractionRing.liftAlgebra R L
  let E := IntermediateField.normalClosure K L (AlgebraicClosure L)
  letI : Algebra S E := ((algebraMap L E).comp (algebraMap S L)).toAlgebra
  letI : IsScalarTower S L E := IsScalarTower.of_algebraMap_eq' rfl
  let T : Type _ := integralClosure S E
  letI : Algebra S T := inferInstance
  letI : Algebra T E := inferInstance
  letI : IsScalarTower S T E := inferInstance
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra R E := ((algebraMap S E).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R T E := IsScalarTower.to₁₃₄ R S T E
  letI : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 <| by
    rw [IsScalarTower.algebraMap_eq R S E]
    exact (algebraMap L E).injective.comp (IsFractionRing.injective S L) |>.comp
      (FaithfulSMul.algebraMap_injective R S)
  letI : IsScalarTower R S L := inferInstance
  letI : FaithfulSMul R L := inferInstance
  letI : IsScalarTower R L E := IsScalarTower.to₁₃₄ R S L E
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  letI : IsScalarTower R K E := IsScalarTower.to₁₂₄ R K L E
  letI : IsIntegralClosure T S E := integralClosure.isIntegralClosure S E
  letI : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).2 <| by
    intro x y hxy
    apply (algebraMap L E).injective.comp (IsFractionRing.injective S L)
    exact congrArg (fun z : T => (algebraMap T E) z) hxy
  letI : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).2 <| by
    rw [IsScalarTower.algebraMap_eq R S T]
    exact (FaithfulSMul.algebraMap_injective S T).comp
      (FaithfulSMul.algebraMap_injective R S)
  letI : FiniteDimensional K E :=
    normalClosure.is_finiteDimensional K L (AlgebraicClosure L)
  letI : Algebra.IsSeparable K E := by
    rw [← le_separableClosure_iff]
    apply normalClosure_le_iff.mpr
    intro i
    haveI : Algebra.IsSeparable K i.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField i)
    exact le_separableClosure K (AlgebraicClosure L) i.fieldRange
  letI : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable K L E
  letI : FiniteDimensional L E := Module.Finite.right K L E
  letI : IsFractionRing T E :=
    IsIntegralClosure.isFractionRing_of_finite_extension S L E T
  letI : Module.Finite S T := IsIntegralClosure.finite S L E T
  letI : Module.Finite R T := Module.Finite.trans S T
  letI : IsDedekindDomain T := integralClosure.isDedekindDomain S L E
  letI : IsGalois K E := {
    to_isSeparable := inferInstance
    to_normal := normalClosure.normal K L (AlgebraicClosure L) }
  let algT : Algebra T (FractionRing T) := inferInstance
  letI : Algebra T (FractionRing T) := algT
  letI : Algebra R (FractionRing T) := inferInstance
  letI : Algebra S (FractionRing T) := inferInstance
  letI : FaithfulSMul R (FractionRing T) := inferInstance
  letI : FaithfulSMul S (FractionRing T) := inferInstance
  letI : Algebra K (FractionRing T) := FractionRing.liftAlgebra R (FractionRing T)
  letI : Algebra L (FractionRing T) := FractionRing.liftAlgebra S (FractionRing T)
  letI : IsScalarTower R K (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra R (FractionRing T)
  letI : IsScalarTower S L (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra S (FractionRing T)
  letI : IsGalois K (FractionRing T) := by
    refine IsGalois.of_equiv_equiv (F := K) (E := E)
      (f := (FractionRing.algEquiv R K).symm.toRingEquiv)
      (g := (FractionRing.algEquiv T E).symm.toRingEquiv) ?_
    ext
    simpa using! IsFractionRing.algEquiv_commutes (FractionRing.algEquiv R K).symm
      (FractionRing.algEquiv T E).symm _
  obtain ⟨Q, hQ₁, hQ₂⟩ : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  letI : Q.IsMaximal := hQ₁
  letI : Q.LiesOver P := hQ₂
  letI : Q.LiesOver p := LiesOver.trans Q P p
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  letI : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    ← Ideal.inertiaDeg'_eq_inertiaDeg P Q, ← Ideal.inertiaDeg'_eq_inertiaDeg p Q,
    inertiaDeg'_algebra_tower p P Q, pow_mul, pow_left_inj] at h
  exact Nat.ne_zero_iff_zero_lt.mpr <| inertiaDeg'_pos P Q
theorem sum_normalizedFactors_relNorm_of_isSeparable
    [@Algebra.IsSeparable (FractionRing R) (FractionRing S) _ _
      (FractionRing.liftAlgebra R (FractionRing S))]
    (I : Ideal S) (hI : I ≠ ⊥) (w : Ideal R → ℕ) :
    ((normalizedFactors (relNorm R I)).map w).sum =
      ((normalizedFactors I).map fun P =>
        (P.under R).inertiaDeg' P * w (P.under R)).sum := by
  classical
  letI : Algebra (FractionRing R) (FractionRing S) :=
    FractionRing.liftAlgebra R (FractionRing S)
  have aux : ∀ s : Multiset (Ideal S), (∀ P ∈ s, Prime P) →
      ((normalizedFactors (relNorm R s.prod)).map w).sum =
        (s.map fun P => (P.under R).inertiaDeg' P * w (P.under R)).sum := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty =>
        rw [Multiset.prod_zero, map_one]
        simp only [normalizedFactors_one, Multiset.map_zero, Multiset.sum_zero]
    | @cons P s ih =>
        have hP : Prime P := hs P (Multiset.mem_cons_self P s)
        have hs' : ∀ Q ∈ s, Prime Q := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
        have hP0 : P ≠ ⊥ := hP.ne_zero
        have hs0 : s.prod ≠ ⊥ := Multiset.prod_ne_zero fun h =>
          (hs' ⊥ h).ne_zero rfl
        let p : Ideal R := P.under R
        letI : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP0
        letI : p.IsMaximal := Ideal.IsMaximal.under R P
        letI : P.LiesOver p := ⟨rfl⟩
        have hp0 : p ≠ ⊥ := by
          intro hp
          haveI : P.LiesOver (⊥ : Ideal R) := hp ▸ (inferInstance : P.LiesOver p)
          exact hP0 (Ideal.eq_bot_of_liesOver_bot R P)
        have hnorm : relNorm R P = p ^ p.inertiaDeg' P :=
          relNorm_eq_pow_of_isMaximal_of_isSeparable P p
        have hnormP0 : relNorm R P ≠ ⊥ := (relNorm_eq_bot_iff.not.mpr hP0)
        have hnorms0 : relNorm R s.prod ≠ ⊥ :=
          relNorm_eq_bot_iff.not.mpr hs0
        rw [Multiset.prod_cons, map_mul, normalizedFactors_mul hnormP0 hnorms0,
          Multiset.map_add, Multiset.sum_add, hnorm, normalizedFactors_pow,
          UniqueFactorizationMonoid.normalizedFactors_irreducible
            (Ideal.prime_of_isPrime hp0
              (inferInstance : p.IsMaximal).isPrime).irreducible,
          normalize_eq, Multiset.nsmul_singleton]
        simp [ih hs', p]
  let s := normalizedFactors I
  have hsprod : s.prod = I := prod_normalizedFactors_eq_self hI
  calc
    ((normalizedFactors (relNorm R I)).map w).sum =
        ((normalizedFactors (relNorm R s.prod)).map w).sum := by rw [hsprod]
    _ = (s.map fun P => (P.under R).inertiaDeg' P * w (P.under R)).sum := by
      apply aux s
      intro P hP
      exact UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    _ = ((normalizedFactors I).map fun P =>
        (P.under R).inertiaDeg' P * w (P.under R)).sum := rfl
end Ideal
end
end


