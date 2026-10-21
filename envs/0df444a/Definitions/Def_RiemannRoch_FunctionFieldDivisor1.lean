-- Prove2me | Definitions.Def_RiemannRoch_FunctionFieldDivisor1
-- name    : RiemannRoch_FunctionFieldDivisor1
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:29:32.457331+00:00
-- url     : https://prove2.me/theorems/2494371a-9c46-4c40-a854-cac641f9accd
-- title:
--   Degree of a chart place of a function field
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_\infty=\{f\in k(X):\deg f\le0\}$ for the valuation ring at infinity of $k(X)$ (with $\deg f=\deg(\text{numerator})-\deg(\text{denominator})$) and $\mathfrak m_\infty$ for its maximal ideal, $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ and $\mathcal O_{K,\infty}$ for the integral closure of $\mathcal O_\infty$ in $K$. The *chart places* are the elements of $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ (finite and infinite places), $v_P$ is the normalized $P$-adic valuation (file `RiemannRoch_Places`), and $f(P|\mathfrak p)=[\mathcal O/P:R/\mathfrak p]$ denotes the inertia degree of a prime $P$ over the prime $\mathfrak p=P\cap R$ below it.
--
--   This file is the **first of four consecutive parts** of the source module `RiemannRoch/FunctionField/Divisor.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FunctionFieldDivisor2`, `RiemannRoch_FunctionFieldDivisor3`, `RiemannRoch_FunctionFieldDivisor4`). It introduces the degree of a chart place: for a finite place $P\in\operatorname{Spec}^1(\mathcal O_K)$, resp. an infinite place $P\in\operatorname{Spec}^1(\mathcal O_{K,\infty})$,
--   $$\deg P=\dim_k\big(\mathcal O_K/P\big),\qquad\text{resp.}\qquad \deg P=\dim_k\big(\mathcal O_{K,\infty}/P\big).$$
--
--   It also contains the first structural lemmas on this degree:
--
--   1. $\deg P>0$ for every chart place $P$;
--   2. for an infinite place $P$, $\deg P=f(P\,|\,\mathfrak m_\infty)$, the inertia degree of $P$ over the maximal ideal of $\mathcal O_\infty$ (whose residue field is $k$);
--   3. for a finite place $P$ lying over the prime $\mathfrak p=P\cap k[X]$, $\deg P=\dim_k(k[X]/\mathfrak p)\cdot f(P\,|\,\mathfrak p)$.
--
--   These formulas reduce degrees of places of $K$ to degrees of places of $k(X)$ and inertia degrees; the following quarters use them to prove that principal divisors have degree zero. In the chain of definition files it imports `RiemannRoch_Places` and is imported by `RiemannRoch_FunctionFieldDivisor2`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The degree is `FunctionField.Chart.placeDegree k K v`, defined by cases on the sum type `PlaceA k K` as a `Module.finrank` over $k$ of the residue ring. Inertia degrees are Mathlib's `Ideal.inertiaDeg'`. The file also declares a local classical `DecidableEq` instance on $k(X)$, reused by the next quarters.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.1 (degree of a place) and Section 3.1 (relative degree of an extension of places, cf.); the formulas for the chart degree are auxiliary lemmas of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/FunctionField/Divisor.lean

import Mathlib
import Definitions.Def_RiemannRoch_Places

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
local instance instDecidableEqRatFuncDivisorFile : DecidableEq k⟮X⟯ := Classical.decEq _
noncomputable def placeDegree (v : PlaceA k K) : ℕ :=
  match v with
  | Sum.inl w =>
    letI : Field (ringOfIntegers k K ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    Module.finrank k (ringOfIntegers k K ⧸ w.asIdeal)
  | Sum.inr w =>
    letI : Field (infiniteIntegers k K ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    Module.finrank k (infiniteIntegers k K ⧸ w.asIdeal)
theorem placeDegree_pos (v : PlaceA k K) : 0 < placeDegree k K v := by
  rcases v with v | v
  · change 0 < Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal)
    exact Module.finrank_pos
  · change 0 < Module.finrank k (infiniteIntegers k K ⧸ v.asIdeal)
    exact Module.finrank_pos
omit [IsScalarTower k[X] k⟮X⟯ K] in
theorem placeDegree_infinite_eq_inertiaDeg
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    placeDegree k K (Sum.inr v) =
      (v.asIdeal.under (inftyValuationSubring k)).inertiaDeg' v.asIdeal := by
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
  change Module.finrank k (S ⧸ v.asIdeal) = p.inertiaDeg' v.asIdeal
  rw [Ideal.inertiaDeg'_algebraMap]
  have htower := Module.finrank_mul_finrank k (A ⧸ p) (S ⧸ v.asIdeal)
  have hbase : Module.finrank k (A ⧸ p) = 1 := by
    rw [hp]
    exact inftyValuationSubring.finrank_residueField k
  rw [hbase, one_mul] at htower
  exact htower.symm
theorem placeDegree_finite_eq_base_mul_inertiaDeg
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    placeDegree k K (Sum.inl v) =
      Module.finrank k (k[X] ⧸ v.asIdeal.under k[X]) *
        (v.asIdeal.under k[X]).inertiaDeg' v.asIdeal := by
  let S := ringOfIntegers k K
  let p : Ideal k[X] := v.asIdeal.under k[X]
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : p.IsMaximal := Ideal.IsMaximal.under k[X] v.asIdeal
  letI : v.asIdeal.LiesOver p := ⟨rfl⟩
  letI : Field (k[X] ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Algebra (k[X] ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  letI : FiniteDimensional k (k[X] ⧸ p) :=
    finite_of_finite_type_of_isJacobsonRing k _
  letI : FiniteDimensional (k[X] ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg'_pos p v.asIdeal
    rw [Ideal.inertiaDeg'_algebraMap] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  letI : IsScalarTower k (k[X] ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Module.finrank k (S ⧸ v.asIdeal) =
    Module.finrank k (k[X] ⧸ p) * p.inertiaDeg' v.asIdeal
  rw [Ideal.inertiaDeg'_algebraMap]
  exact (Module.finrank_mul_finrank k (k[X] ⧸ p) (S ⧸ v.asIdeal)).symm
end FunctionField.Chart
end
end
end


