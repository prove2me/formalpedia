-- Prove2me | Definitions.Def_RiemannRoch_FunctionFieldDivisor3
-- name    : RiemannRoch_FunctionFieldDivisor3
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:33:58.344983+00:00
-- url     : https://prove2.me/theorems/80cfdd93-abbd-47af-8147-ebea8b194676
-- title:
--   Norm and factor-counting lemmas for the two charts; prime weights $\deg P$
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places). Write $N$ for the relative norm of ideals (from $\mathcal O_K$ to $k[X]$, resp. from $\mathcal O_{K,\infty}$ to $\mathcal O_\infty$) and also for the norm of integral elements, $N_{K/k(X)}$ for the field norm, and $f(P|\mathfrak p)$ for the inertia degree.
--
--   This file is the **third of four consecutive parts** of the source module `RiemannRoch/FunctionField/Divisor.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FunctionFieldDivisor1`, `RiemannRoch_FunctionFieldDivisor2`, `RiemannRoch_FunctionFieldDivisor4`). It introduces the two **prime weights** used to count degrees prime by prime: for a prime $P$ of $\mathcal O_K$, resp. of $\mathcal O_{K,\infty}$,
--   $$w_{\mathrm{fin}}(P)=\dim_k\big(k[X]/(P\cap k[X])\big)\cdot f\big(P\,|\,P\cap k[X]\big),\qquad w_\infty(P)=f\big(P\,|\,P\cap\mathcal O_\infty\big),$$
--   which are the degrees of the corresponding chart places.
--
--   It also contains the structural lemmas used for the degree of principal divisors (prime factors are counted with multiplicity):
--
--   1. for a nonzero ideal $I$ of $\mathcal O_{K,\infty}$, $\sum_{P\mid I}f(P|P\cap\mathcal O_\infty)$ equals the number of prime factors of $N(I)$ in $\mathcal O_\infty$ (the infinite analogue of the previous quarter);
--   2. for $0\ne p\in k[X]$, $\sum_{\mathfrak q\mid(p)}\dim_k(k[X]/\mathfrak q)=\deg p$;
--   3. for $0\ne a\in\mathcal O_\infty$, the number of prime factors of $a\mathcal O_\infty$ is $-\deg a$;
--   4. if $x\in K^\times$ is written $x=n/d$ with $n,d\in\mathcal O_K$, $d\ne0$, then $N(n)/N(d)=N_{K/k(X)}(x)$ in $k(X)$, and likewise with $n,d\in\mathcal O_{K,\infty}$ and norms to $\mathcal O_\infty$.
--
--   In the chain of definition files it imports `RiemannRoch_FunctionFieldDivisor2` and is imported by `RiemannRoch_FunctionFieldDivisor4`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The weights are `FunctionField.Chart.finiteIdealWeight` and `infiniteIdealWeight` (functions on all ideals, with values in $\mathbb N$). Element norms are Mathlib's `Algebra.intNorm`, the fractions $n/d$ are `IsLocalization.mk' K n d`, the field norm is `Algebra.norm k⟮X⟯` and $\deg$ on $k(X)$ is `RatFunc.intDegree`.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4 (degree of principal divisors, cf. Theorem 1.4.11 and its corollary) and Section 3.1 (relative degree, cf.); the norm and factor-counting identities are auxiliary lemmas of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/FunctionField/Divisor.lean

import Mathlib
import Definitions.Def_RiemannRoch_FunctionFieldDivisor2

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
open scoped nonZeroDivisors Polynomial RatFunc
noncomputable section
namespace FunctionField.Chart
variable (k K : Type*) [Field k] [Field K]
  [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
attribute [local instance] FunctionField.Chart.instDecidableEqRatFuncDivisorFile
omit [Algebra k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
theorem infinite_factorDegree_eq_relNorm
    (I : Ideal (infiniteIntegers k K)) (hI : I ≠ ⊥) :
    ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
      (P.under (inftyValuationSubring k)).inertiaDeg' P).sum =
    ((UniqueFactorizationMonoid.normalizedFactors
      (Ideal.relNorm (inftyValuationSubring k) I)).map fun _ => 1).sum := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  letI : Algebra A (FractionRing S) := inferInstance
  letI : FaithfulSMul A (FractionRing S) := inferInstance
  letI : Algebra (FractionRing A) (FractionRing S) :=
    FractionRing.liftAlgebra A (FractionRing S)
  letI : IsScalarTower A (FractionRing A) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A k⟮X⟯).symm.toRingEquiv
      (FractionRing.algEquiv S K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv A k⟮X⟯).symm
      (FractionRing.algEquiv S K).symm x
  symm
  simpa using Ideal.sum_normalizedFactors_relNorm_of_isSeparable I hI
    (fun _ : Ideal A => 1)
theorem polynomial_factorDegree_span (p : k[X]) (hp : p ≠ 0) :
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {p})).map
      (fun P : Ideal k[X] => Module.finrank k (k[X] ⧸ P))).sum = p.natDegree := by
  classical
  rw [← UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    Ideal.factors_span_eq, Multiset.map_map]
  simp_rw [Function.comp_apply, finrank_quotient_span_eq_natDegree]
  have hassoc := UniqueFactorizationMonoid.factors_prod hp
  have hprod : (UniqueFactorizationMonoid.factors p).prod ≠ 0 :=
    hassoc.ne_zero_iff.mpr hp
  have hzero : (0 : k[X]) ∉ UniqueFactorizationMonoid.factors p := by
    intro h
    exact hprod (Multiset.prod_eq_zero_iff.mpr h)
  rw [← Polynomial.natDegree_multiset_prod _ hzero]
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated hassoc)
theorem infinity_factorDegree_span (a : inftyValuationSubring k) (ha : a ≠ 0) :
    ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).map
      (fun _ : Ideal (inftyValuationSubring k) => (1 : ℕ))).sum : ℕ) : ℤ) =
        -RatFunc.intDegree (a : k⟮X⟯) := by
  classical
  let v := RatFunc.inftyValuation k
  let A := inftyValuationSubring k
  have hmem : (1 / RatFunc.X : k⟮X⟯) ∈ v.valuationSubring := by
    change v (1 / RatFunc.X) ≤ 1
    rw [RatFunc.inftyValuation.X_inv]
    simpa only [← WithZero.exp_zero, WithZero.exp_le_exp] using (show (-1 : ℤ) ≤ 0 by omega)
  let π : v.valuationSubring := ⟨1 / RatFunc.X, hmem⟩
  have hgen : (↑(Valuation.IsRankOneDiscrete.generator v) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
    have h := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      (v := v) (show WithZero.exp (-1 : ℤ) ∈ Set.range v from
        ⟨1 / RatFunc.X, RatFunc.inftyValuation.X_inv k⟩)
    exact congrArg Units.val h
  have hπval : v (π : k⟮X⟯) = WithZero.exp (-1 : ℤ) := by
    exact RatFunc.inftyValuation.X_inv k
  have hπ : v.IsUniformizer (π : k⟮X⟯) := by
    rw [Valuation.IsUniformizer.iff, hgen]
    exact hπval
  let πu : v.Uniformizer := ⟨π, hπ⟩
  obtain ⟨n, u, hau⟩ := Valuation.exists_pow_Uniformizer ha πu
  have hassocA : Associated a (π ^ n) := by
    have hauA : a = π ^ n * (u : v.valuationSubring) := by
      apply Subtype.ext
      exact hau
    rw [hauA]
    exact associated_mul_unit_left _ _ u.isUnit
  have hmaxpow : IsLocalRing.maximalIdeal A ^ n = Ideal.span {π ^ n} := by
    exact Valuation.pow_Uniformizer_is_pow_generator πu n
  have hideal : Ideal.span {a} = IsLocalRing.maximalIdeal A ^ n := by
    rw [hmaxpow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassocA
  have hmaxIrred : Irreducible (IsLocalRing.maximalIdeal A) := by
    exact (Ideal.prime_of_isPrime
      (IsDiscreteValuationRing.maximalIdeal A).ne_bot
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime).irreducible
  have hfactor :
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}) =
        Multiset.replicate n (IsLocalRing.maximalIdeal A) := by
    rw [hideal, UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hmaxIrred,
      normalize_eq, Multiset.nsmul_singleton]
  have hleft :
      ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).map
        (fun _ : Ideal A => 1)).sum = n := by
    rw [hfactor]
    simp
  have huval : v ((u : v.valuationSubring) : k⟮X⟯) = 1 := by
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers v)).mp u.isUnit
  have haval : v (a : k⟮X⟯) = WithZero.exp (RatFunc.intDegree (a : k⟮X⟯)) := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero]
    simpa using ha
  have hvrepr := congrArg v hau
  have hexp : WithZero.exp (RatFunc.intDegree (a : k⟮X⟯)) =
      WithZero.exp (-(n : ℤ)) := by
    rw [← haval, hvrepr, map_mul]
    change v ((π : k⟮X⟯) ^ n) * v ((u : v.valuationSubring) : k⟮X⟯) = _
    rw [map_pow, hπval, huval, mul_one]
    calc
      WithZero.exp (-1 : ℤ) ^ n = WithZero.exp (n • (-1 : ℤ)) :=
        (WithZero.exp_nsmul n (-1 : ℤ)).symm
      _ = WithZero.exp (-(n : ℤ)) := by congr 1; simp
  have hint : RatFunc.intDegree (a : k⟮X⟯) = -(n : ℤ) :=
    WithZero.exp_injective hexp
  have hleftZ :
      ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).map
        (fun _ : Ideal A => (1 : ℕ))).sum : ℕ) : ℤ) = (n : ℤ) := by
    exact congrArg (fun m : ℕ => (m : ℤ)) hleft
  rw [hleftZ, hint]
  omega
theorem finite_intNorm_div_eq_norm (x : Kˣ) (n : ringOfIntegers k K)
    (d : nonZeroDivisors (ringOfIntegers k K))
    (hnd : IsLocalization.mk' K n d = (x : K)) :
    algebraMap k[X] k⟮X⟯ (Algebra.intNorm k[X] (ringOfIntegers k K) n) /
      algebraMap k[X] k⟮X⟯
        (Algebra.intNorm k[X] (ringOfIntegers k K) (d : ringOfIntegers k K)) =
      Algebra.norm k⟮X⟯ (x : K) := by
  have hn : algebraMap k[X] k⟮X⟯ (Algebra.intNorm k[X] (ringOfIntegers k K) n) =
      Algebra.intNorm k⟮X⟯ K (algebraMap (ringOfIntegers k K) K n) :=
    Algebra.intNorm_eq_of_isLocalization k[X]⁰ (Bₘ := K) n
  have hd : algebraMap k[X] k⟮X⟯
      (Algebra.intNorm k[X] (ringOfIntegers k K) (d : ringOfIntegers k K)) =
      Algebra.intNorm k⟮X⟯ K
        (algebraMap (ringOfIntegers k K) K (d : ringOfIntegers k K)) :=
    Algebra.intNorm_eq_of_isLocalization k[X]⁰ (Bₘ := K) (d : ringOfIntegers k K)
  rw [Algebra.intNorm_eq_norm k[X] (ringOfIntegers k K),
    Algebra.intNorm_eq_norm k⟮X⟯ K] at hn hd
  let N : K →*₀ k⟮X⟯ :=
    { Algebra.norm k⟮X⟯ with
      map_zero' := (Algebra.norm_eq_zero_iff (R := k⟮X⟯) (S := K)).mpr rfl }
  have hx := congrArg N hnd
  rw [IsFractionRing.mk'_eq_div, map_div₀] at hx
  change Algebra.norm k⟮X⟯ (algebraMap (ringOfIntegers k K) K n) /
    Algebra.norm k⟮X⟯
      (algebraMap (ringOfIntegers k K) K (d : ringOfIntegers k K)) =
      Algebra.norm k⟮X⟯ (x : K) at hx
  rw [← hn, ← hd] at hx
  simpa [Algebra.intNorm_eq_norm k[X] (ringOfIntegers k K)] using hx
omit [Algebra k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
theorem infinite_intNorm_div_eq_norm (x : Kˣ) (n : infiniteIntegers k K)
    (d : nonZeroDivisors (infiniteIntegers k K))
    (hnd : IsLocalization.mk' K n d = (x : K)) :
    algebraMap (inftyValuationSubring k) k⟮X⟯
        (Algebra.intNorm (inftyValuationSubring k) (infiniteIntegers k K) n) /
      algebraMap (inftyValuationSubring k) k⟮X⟯
        (Algebra.intNorm (inftyValuationSubring k) (infiniteIntegers k K)
          (d : infiniteIntegers k K)) =
      Algebra.norm k⟮X⟯ (x : K) := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  have hn : algebraMap A k⟮X⟯ (Algebra.intNorm A S n) =
      Algebra.intNorm k⟮X⟯ K (algebraMap S K n) :=
    Algebra.intNorm_eq_of_isLocalization A⁰ (Bₘ := K) n
  have hd : algebraMap A k⟮X⟯ (Algebra.intNorm A S (d : S)) =
      Algebra.intNorm k⟮X⟯ K (algebraMap S K (d : S)) :=
    Algebra.intNorm_eq_of_isLocalization A⁰ (Bₘ := K) (d : S)
  rw [Algebra.intNorm_eq_norm A S, Algebra.intNorm_eq_norm k⟮X⟯ K] at hn hd
  let N : K →*₀ k⟮X⟯ :=
    { Algebra.norm k⟮X⟯ with
      map_zero' := (Algebra.norm_eq_zero_iff (R := k⟮X⟯) (S := K)).mpr rfl }
  have hx := congrArg N hnd
  rw [IsFractionRing.mk'_eq_div, map_div₀] at hx
  change Algebra.norm k⟮X⟯ (algebraMap S K n) /
    Algebra.norm k⟮X⟯ (algebraMap S K (d : S)) = Algebra.norm k⟮X⟯ (x : K) at hx
  rw [← hn, ← hd] at hx
  simpa [A, S, Algebra.intNorm_eq_norm A S] using hx
noncomputable def finiteIdealWeight (P : Ideal (ringOfIntegers k K)) : ℕ :=
  Module.finrank k (k[X] ⧸ P.under k[X]) * (P.under k[X]).inertiaDeg' P
noncomputable def infiniteIdealWeight (P : Ideal (infiniteIntegers k K)) : ℕ :=
  (P.under (inftyValuationSubring k)).inertiaDeg' P
end FunctionField.Chart
end
end
end


