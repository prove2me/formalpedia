-- Prove2me | Definitions.Def_RiemannRoch_FunctionFieldDivisor4
-- name    : RiemannRoch_FunctionFieldDivisor4
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:37:30.959274+00:00
-- url     : https://prove2.me/theorems/3f04d101-4d2a-422e-80cd-74bfb4c87e63
-- title:
--   Degree of chart divisors, $\deg\operatorname{div}(x)=0$, full constant field and local residue maps
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation, $\deg P$ is the degree of a chart place (first quarter) and a chart divisor is a finitely supported function $D:\mathbb P^{\mathrm{ch}}_K\to\mathbb Z$.
--
--   This file is the **fourth of four consecutive parts** of the source module `RiemannRoch/FunctionField/Divisor.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FunctionFieldDivisor1`, `RiemannRoch_FunctionFieldDivisor2`, `RiemannRoch_FunctionFieldDivisor3`). It is followed by the short modules `RiemannRoch/Basic.lean` and `RiemannRoch/LocalResidue.lean`. It introduces:
--
--   1. the valuation subring $\mathcal O_P=\{f\in K: v_P(f)\ge0\}$ of a chart place $P$;
--   2. the **degree of a chart divisor**
--   $$\deg D=\sum_{P\in\mathbb P^{\mathrm{ch}}_K}D(P)\,\deg P,$$
--   together with the support $\operatorname{supp}D=\{P: D(P)\ne0\}$ and effectivity ($D\ge0$ means $D(P)\ge0$ for all $P$; the order $D\le D'$ is pointwise);
--   3. the **full constant field** condition: $k$ is the full constant field of $K$ if every element of $K$ algebraic over $k$ lies in $k$; this holds for $K=k(X)$;
--   4. for a height-one prime $\mathfrak p$ of a Dedekind domain $R$ with fraction field $L$, the **residue map** $R_{\mathfrak p}\to\kappa(\mathfrak p)$ from the valuation ring at $\mathfrak p$ onto the residue field, and the identification of the localization $R_{\mathfrak p}$ with the valuation subring of $L$ at $\mathfrak p$.
--
--   It also contains the structural lemmas: for $x\in K^\times$ the finite part of the principal divisor has degree $\sum_{P\text{ finite}}v_P(x)\deg P=\deg N_{K/k(X)}(x)$ and the infinite part has degree $-\deg N_{K/k(X)}(x)$, so that
--   $$\deg\operatorname{div}(x)=0;$$
--   $\deg$ is additive ($\deg0=0$, $\deg(D_1+D_2)=\deg D_1+\deg D_2$, $\deg(-D)=-\deg D$, $\deg(D-D')=\deg D-\deg D'$, $\deg(nD)=n\deg D$ for $n\in\mathbb N$), $\deg(n\cdot P)=n\deg P$, $\deg$ is monotone, $\deg D\ge0$ for $D\ge0$ with equality only for $D=0$, and $D\le D'$ iff $D'-D\ge0$; finally the residue map kills exactly the elements of positive valuation and sends $n/d$ ($d\notin\mathfrak p$) to $\bar n\,\bar d^{-1}$.
--
--   The degree of divisors and the formula $\deg\operatorname{div}(x)=0$ are the basic numerical invariants entering the Riemann–Roch theorem; the full constant field is its standing hypothesis. In the chain of definition files it imports `RiemannRoch_FunctionFieldDivisor3` and is imported by `RiemannRoch_RRSpace`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The degree is `FunctionField.Chart.deg k K D` (aliases `FunctionField.degA`, `placeDegA`), $\deg$ on $k(X)$ is `RatFunc.intDegree`, and the partial order on divisors is Mathlib's pointwise order on `Finsupp` (no new order instance). The full constant field hypothesis is the class `FunctionField.IsFullConstantField k K` (every $x\in K$ with `IsAlgebraic k x` is of the form `algebraMap k K c`), with an instance for `RatFunc k`. The residue map is `IsDedekindDomain.HeightOneSpectrum.residueHom`, from Mathlib's `valuationSubringAtPrime K v` to `v.asIdeal.ResidueField`; its kernel is described as $\{z: \text{valuation of }z<1\}$ in the multiplicative convention.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4 (degree of a divisor, effective divisors, degree of principal divisors: cf. Theorem 1.4.11 and its corollary $\deg(x)=0$); full constant field: the standing assumption of Stichtenoth from Section 1.1 on; the norm computations and residue maps are auxiliary lemmas of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/FunctionField/Divisor.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/Basic.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/LocalResidue.lean

import Mathlib
import Definitions.Def_RiemannRoch_FunctionFieldDivisor3

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
theorem finitePrincipalDegree_eq_intDegree_norm (x : Kˣ) :
    (FractionalIdeal.principalDivisor
      (R := ringOfIntegers k K) (K := K) (Additive.ofMul x)).sum
        (fun v n => n * (placeDegree k K (Sum.inl v) : ℤ)) =
      RatFunc.intDegree (Algebra.norm k⟮X⟯ (x : K)) := by
  classical
  let S := ringOfIntegers k K
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq S⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn
    exact x.ne_zero (by simpa [hn] using hnd.symm)
  have hd : (d : S) ≠ 0 := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero] using d.property
  have hdeg := FractionalIdeal.weightedDegree_principal_mk'
    (R := S) (K := K) (finiteIdealWeight k K) x n d hnd
  have hnormn := finite_factorDegree_eq_relNorm k K (Ideal.span {n})
    (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hnormd := finite_factorDegree_eq_relNorm k K (Ideal.span {(d : S)})
    (Ideal.span_singleton_eq_bot.not.mpr hd)
  let pn : k[X] := Algebra.intNorm k[X] S n
  let pd : k[X] := Algebra.intNorm k[X] S (d : S)
  have hpn : pn ≠ 0 := by
    dsimp only [pn]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hn
  have hpd : pd ≠ 0 := by
    dsimp only [pd]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hd
  rw [Ideal.relNorm_singleton, polynomial_factorDegree_span k pn hpn] at hnormn
  rw [Ideal.relNorm_singleton, polynomial_factorDegree_span k pd hpd] at hnormd
  change
    (FractionalIdeal.principalDivisor
      (R := S) (K := K) (Additive.ofMul x)).sum
        (fun v m => m * (placeDegree k K (Sum.inl v) : ℤ)) = _
  have hchart :
      (FractionalIdeal.principalDivisor
        (R := S) (K := K) (Additive.ofMul x)).sum
          (fun v m => m * (placeDegree k K (Sum.inl v) : ℤ)) =
        (pn.natDegree : ℤ) - (pd.natDegree : ℤ) := by
    rw [← hnormn, ← hnormd]
    unfold finiteIdealWeight at hdeg
    simpa only [FractionalIdeal.weightedDegree_apply, finiteIdealWeight,
      placeDegree_finite_eq_base_mul_inertiaDeg] using hdeg
  have hratio := finite_intNorm_div_eq_norm k K x n d hnd
  change algebraMap k[X] k⟮X⟯ pn / algebraMap k[X] k⟮X⟯ pd =
    Algebra.norm k⟮X⟯ (x : K) at hratio
  have hpn' : algebraMap k[X] k⟮X⟯ pn ≠ 0 :=
    by simpa using (IsFractionRing.injective k[X] k⟮X⟯).ne hpn
  have hpd' : algebraMap k[X] k⟮X⟯ pd ≠ 0 :=
    by simpa using (IsFractionRing.injective k[X] k⟮X⟯).ne hpd
  have hint := congrArg RatFunc.intDegree hratio
  rw [RatFunc.intDegree_div hpn' hpd', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial] at hint
  exact hchart.trans hint
omit [IsScalarTower k[X] k⟮X⟯ K] in
theorem infinitePrincipalDegree_eq_neg_intDegree_norm (x : Kˣ) :
    (FractionalIdeal.principalDivisor
      (R := infiniteIntegers k K) (K := K) (Additive.ofMul x)).sum
        (fun v n => n * (placeDegree k K (Sum.inr v) : ℤ)) =
      -RatFunc.intDegree (Algebra.norm k⟮X⟯ (x : K)) := by
  classical
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq S⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn
    exact x.ne_zero (by simpa [hn] using hnd.symm)
  have hd : (d : S) ≠ 0 := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero] using d.property
  have hdeg := FractionalIdeal.weightedDegree_principal_mk'
    (R := S) (K := K) (infiniteIdealWeight k K) x n d hnd
  have hnormn := infinite_factorDegree_eq_relNorm k K (Ideal.span {n})
    (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hnormd := infinite_factorDegree_eq_relNorm k K (Ideal.span {(d : S)})
    (Ideal.span_singleton_eq_bot.not.mpr hd)
  let qn : A := Algebra.intNorm A S n
  let qd : A := Algebra.intNorm A S (d : S)
  have hqn : qn ≠ 0 := by
    dsimp only [qn]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hn
  have hqd : qd ≠ 0 := by
    dsimp only [qd]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hd
  rw [Ideal.relNorm_singleton] at hnormn hnormd
  have hbaseqn := infinity_factorDegree_span k qn hqn
  have hbaseqd := infinity_factorDegree_span k qd hqd
  have hnormnZ := congrArg (fun m : ℕ => (m : ℤ)) hnormn
  have hnormdZ := congrArg (fun m : ℕ => (m : ℤ)) hnormd
  have hupn :
      ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).map
        (fun P => (P.under (inftyValuationSubring k)).inertiaDeg' P)).sum : ℕ) : ℤ) =
          -RatFunc.intDegree (qn : k⟮X⟯) :=
    hnormnZ.trans hbaseqn
  have hupd :
      ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(d : S)})).map
        (fun P => (P.under (inftyValuationSubring k)).inertiaDeg' P)).sum : ℕ) : ℤ) =
          -RatFunc.intDegree (qd : k⟮X⟯) :=
    hnormdZ.trans hbaseqd
  change
    (FractionalIdeal.principalDivisor
      (R := S) (K := K) (Additive.ofMul x)).sum
        (fun v m => m * (placeDegree k K (Sum.inr v) : ℤ)) = _
  have hchart :
      (FractionalIdeal.principalDivisor
        (R := S) (K := K) (Additive.ofMul x)).sum
          (fun v m => m * (placeDegree k K (Sum.inr v) : ℤ)) =
        -RatFunc.intDegree (qn : k⟮X⟯) -
          (-RatFunc.intDegree (qd : k⟮X⟯)) := by
    have hdeg' := hdeg
    unfold infiniteIdealWeight at hdeg'
    simp only [FractionalIdeal.weightedDegree_apply, infiniteIdealWeight] at hdeg'
    rw [hupn, hupd] at hdeg'
    simpa only [placeDegree_infinite_eq_inertiaDeg] using hdeg'
  have hratio := infinite_intNorm_div_eq_norm k K x n d hnd
  change (qn : k⟮X⟯) / (qd : k⟮X⟯) = Algebra.norm k⟮X⟯ (x : K) at hratio
  have hqn' : (qn : k⟮X⟯) ≠ 0 := by simpa using hqn
  have hqd' : (qd : k⟮X⟯) ≠ 0 := by simpa using hqd
  have hint := congrArg RatFunc.intDegree hratio
  rw [RatFunc.intDegree_div hqn' hqd'] at hint
  rw [hchart, ← hint]
  ring
noncomputable def placeValuationSubring (v : PlaceA k K) : ValuationSubring K :=
  (placeValuation k K v).valuationSubring
noncomputable def deg (D : DivisorA k K) : ℤ :=
  D.sum fun v n => (n : ℤ) * (placeDegree k K v : ℤ)
theorem deg_principalDivisorA_eq_zero (x : Kˣ) :
    deg k K (principalDivisorA k K (Additive.ofMul x)) = 0 := by
  let Dfin := FractionalIdeal.principalDivisor
    (R := ringOfIntegers k K) (K := K) (Additive.ofMul x)
  let Dinf := FractionalIdeal.principalDivisor
    (R := infiniteIntegers k K) (K := K) (Additive.ofMul x)
  have hdiv : principalDivisorA k K (Additive.ofMul x) = Dfin.sumElim Dinf := by
    rw [Finsupp.sumElim_eq_add]
    rfl
  rw [deg, hdiv, Finsupp.sum_sumElim]
  change
    Dfin.sum (fun v n => n * (placeDegree k K (Sum.inl v) : ℤ)) +
      Dinf.sum (fun v n => n * (placeDegree k K (Sum.inr v) : ℤ)) = 0
  rw [finitePrincipalDegree_eq_intDegree_norm k K x,
    infinitePrincipalDegree_eq_neg_intDegree_norm k K x]
  exact add_neg_cancel _
def support (D : DivisorA k K) : Finset (PlaceA k K) := D.support
def IsEffective (D : DivisorA k K) : Prop :=
  ∀ v, 0 ≤ D v
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_zero : deg k K (0 : DivisorA k K) = 0 := by
  simp [deg, placeDegree]
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_add (D₁ D₂ : DivisorA k K) :
    deg k K (D₁ + D₂) = deg k K D₁ + deg k K D₂ := by
  classical
  simp [deg, Finsupp.sum_add_index, add_mul]
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_neg (D : DivisorA k K) : deg k K (-D) = -deg k K D := by
  classical
  simp [deg, Finsupp.sum_neg_index, neg_mul]
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_sub (D D' : DivisorA k K) :
    deg k K (D - D') = deg k K D - deg k K D' := by
  simp [deg_add, deg_neg, sub_eq_add_neg]
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_nsmul {D : DivisorA k K} (n : ℕ) :
    deg k K (n • D) = (n : ℤ) * deg k K D := by
  induction n with
  | zero => simp [deg_zero]
  | succ n ih =>
      rw [succ_nsmul, deg_add, ih]
      simp only [Nat.cast_add, Nat.cast_one, one_mul, add_mul, add_comm]
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_nonneg {D : DivisorA k K} (hD : IsEffective k K D) :
    0 ≤ deg k K D := by
  classical
  exact Finsupp.sum_nonneg fun v _ =>
    mul_nonneg (hD v) (Int.natCast_nonneg (placeDegree k K v))
theorem eq_zero_of_effective_deg_zero {D : DivisorA k K} (hD : IsEffective k K D)
    (hdeg : deg k K D = 0) : D = 0 := by
  classical
  rw [deg, Finsupp.sum] at hdeg
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
    mul_nonneg (hD v) (Int.natCast_nonneg (placeDegree k K v)))).1 hdeg
  apply Finsupp.ext
  intro v
  simp only [Finsupp.zero_apply]
  by_cases hv : v ∈ D.support
  · have hmul := hall v hv
    have hplace : (placeDegree k K v : ℤ) ≠ 0 := by
      exact_mod_cast (placeDegree_pos k K v).ne'
    exact (mul_eq_zero.mp hmul).resolve_right hplace
  · simpa only [Finsupp.mem_support_iff, not_not] using hv
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_single (v : PlaceA k K) (n : ℤ) :
    deg k K (Finsupp.single v n) = n * placeDegree k K v := by
  simp [deg, Finsupp.sum_single_index]
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_mono {D D' : DivisorA k K} (h : D ≤ D') :
    deg k K D ≤ deg k K D' := by
  rw [← sub_nonneg, ← deg_sub]
  apply deg_nonneg k K
  intro v
  exact sub_nonneg.mpr (h v)
omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem le_iff_sub_effective {D D' : DivisorA k K} :
    D ≤ D' ↔ IsEffective k K (D' - D) := by
  simp only [Finsupp.le_def, IsEffective, Finsupp.sub_apply, sub_nonneg]
end FunctionField.Chart
end
end
end

section
section
open scoped nonZeroDivisors Polynomial RatFunc
noncomputable section
namespace FunctionField
open Chart
variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]
abbrev placeDegA (v : PlaceA k K) : ℕ := placeDegree k K v
noncomputable abbrev degA (D : DivisorA k K) : ℤ := deg k K D
class IsFullConstantField (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop where
  algebraic_mem : ∀ x : K, IsAlgebraic k x → ∃ c : k, x = algebraMap k K c
namespace IsFullConstantField
variable (k K : Type*) [Field k] [Field K] [Algebra k K] [IsFullConstantField k K]
end IsFullConstantField
instance ratFuncIsFullConstantField : IsFullConstantField k (RatFunc k) where
  algebraic_mem x hx := by
    by_contra h
    exact RatFunc.transcendental_of_ne_C x h hx
end FunctionField
end
end
end

section
section
open scoped nonZeroDivisors WithZero
noncomputable section
open IsDedekindDomain
namespace IsDedekindDomain.HeightOneSpectrum
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
noncomputable def residueHom (v : HeightOneSpectrum R) :
    valuationSubringAtPrime K v →+* v.asIdeal.ResidueField :=
  IsLocalization.lift (S := valuationSubringAtPrime K v)
    (g := algebraMap R v.asIdeal.ResidueField)
    fun y : v.asIdeal.primeCompl => isUnit_iff_ne_zero.mpr <| by
      rw [ne_eq, Ideal.algebraMap_residueField_eq_zero]
      exact Ideal.mem_primeCompl_iff.mp y.property
theorem residueHom_eq_zero_iff (v : HeightOneSpectrum R)
    (z : valuationSubringAtPrime K v) :
    residueHom (K := K) v z = 0 ↔ v.valuation K (z : K) < 1 := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq v.asIdeal.primeCompl z
  rw [← hnd, residueHom, IsLocalization.lift_mk']
  simp only [mul_eq_zero, Units.ne_zero, or_false]
  rw [Ideal.algebraMap_residueField_eq_zero]
  rw [← valuation_lt_one_iff_mem (K := K) v]
  rw [show (↑(IsLocalization.mk' (valuationSubringAtPrime K v) n d) : K) =
      algebraMap R K n / algebraMap R K d by
    have hd0 : (d : R) ≠ 0 := by
      intro hd
      exact (Ideal.mem_primeCompl_iff.mp d.property) (hd ▸ v.asIdeal.zero_mem)
    have hdK : algebraMap R K (d : R) ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0
    apply (eq_div_iff hdK).2
    have h := congrArg (fun y : valuationSubringAtPrime K v => (y : K))
      (IsLocalization.mk'_spec (valuationSubringAtPrime K v) n d)
    change (↑(IsLocalization.mk' (valuationSubringAtPrime K v) n d) : K) *
      algebraMap R K d = algebraMap R K n at h
    exact h]
  rw [(v.valuation K).map_div]
  have hvd : v.valuation K (algebraMap R K d) = 1 :=
    (valuation_eq_one_iff_notMem (K := K) (v := v)).2
      (Ideal.mem_primeCompl_iff.mp d.property)
  rw [hvd, div_one]
noncomputable def localizationAlgEquiv (v : HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal ≃ₐ[R] valuationSubringAtPrime K v :=
  IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal)
    (valuationSubringAtPrime K v)
theorem residueHom_mk' (v : HeightOneSpectrum R) (n : R) (d : v.asIdeal.primeCompl) :
    residueHom (K := K) v (IsLocalization.mk' (valuationSubringAtPrime K v) n d) =
      algebraMap R v.asIdeal.ResidueField n *
        (algebraMap R v.asIdeal.ResidueField (d : R))⁻¹ := by
  dsimp [residueHom]
  simp [IsLocalization.lift_mk', IsUnit.coe_liftRight]
theorem residueHom_mk'_residue (v : HeightOneSpectrum R) (n : R) (d : v.asIdeal.primeCompl) :
    residueHom (K := K) v (IsLocalization.mk' (valuationSubringAtPrime K v) n d) =
      IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        (IsLocalization.mk' (Localization.AtPrime v.asIdeal) n d) := by
  have hd0 : algebraMap R v.asIdeal.ResidueField (d : R) ≠ 0 :=
    Ideal.algebraMap_residueField_eq_zero.not.mpr (Ideal.mem_primeCompl_iff.mp d.property)
  have hdunit : IsUnit (algebraMap R v.asIdeal.ResidueField (d : R)) :=
    isUnit_iff_ne_zero.mpr hd0
  rw [residueHom_mk', mul_inv_eq_iff_eq_mul₀ hd0]
  have h := congrArg (IsLocalRing.residue (Localization.AtPrime v.asIdeal))
    (IsLocalization.mk'_spec (S := Localization.AtPrime v.asIdeal) n d)
  rw [map_mul] at h
  rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) v.asIdeal.ResidueField n,
    IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) v.asIdeal.ResidueField (d : R),
    ← IsLocalRing.ResidueField.algebraMap_eq] at *
  exact h.symm
theorem residueHom_apply_localizationAlgEquiv (v : HeightOneSpectrum R)
    (x : Localization.AtPrime v.asIdeal) :
    residueHom (K := K) v (localizationAlgEquiv (K := K) v x) =
      IsLocalRing.residue (Localization.AtPrime v.asIdeal) x := by
  obtain ⟨n, d, hx⟩ := IsLocalization.exists_mk'_eq v.asIdeal.primeCompl x
  rw [← hx]
  simp [localizationAlgEquiv, residueHom_mk'_residue]
end IsDedekindDomain.HeightOneSpectrum
end
end
end


