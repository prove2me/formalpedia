-- Prove2me | Definitions.Def_RiemannRoch_FunctionFieldDivisor2
-- name    : RiemannRoch_FunctionFieldDivisor2
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T11:30:27.393979+00:00
-- url     : https://prove2.me/theorems/42688dd4-159e-4027-b9e8-38ab49ee444e
-- title:
--   Prime-factor degree sums and relative norms on the finite chart
-- statement:
--   Throughout, $k$ is a field and $K$ is a field together with compatible embeddings $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is a finite separable extension; $K$ is thus an algebraic function field in one variable over $k$, presented together with the transcendental element $x=X\in K$. Write $\mathcal O_K$ for the integral closure of $k[X]$ in $K$ (a Dedekind domain, finite over $k[X]$), $N(I)\subseteq k[X]$ for the relative norm of an ideal $I$ of $\mathcal O_K$, and $f(P|\mathfrak p)$ for the inertia degree of a prime $P$ of $\mathcal O_K$ over $\mathfrak p=P\cap k[X]$.
--
--   This file is the **second of four consecutive parts** of the source module `RiemannRoch/FunctionField/Divisor.lean`, which was cut into quarters for publication (the other parts are `RiemannRoch_FunctionFieldDivisor1`, `RiemannRoch_FunctionFieldDivisor3`, `RiemannRoch_FunctionFieldDivisor4`). It introduces **no new definition**: it consists of a single structural lemma, the finite-chart case of the comparison between degrees upstairs and downstairs. For every nonzero ideal $I$ of $\mathcal O_K$,
--   $$\sum_{P\mid I}\dim_k\big(k[X]/(P\cap k[X])\big)\,f\big(P\,|\,P\cap k[X]\big)\;=\;\sum_{\mathfrak q\mid N(I)}\dim_k\big(k[X]/\mathfrak q\big),$$
--   where on the left $P$ runs over the prime factors of $I$ and on the right $\mathfrak q$ over the prime factors of $N(I)$, both counted with multiplicity.
--
--   By the previous quarter the left-hand summands are the degrees $\deg P$ of the finite chart places, so this identity expresses the degree of the finite part of the divisor of an ideal through its norm in $k[X]$, a step towards $\deg\operatorname{div}(x)=0$. In the chain of definition files it imports `RiemannRoch_FunctionFieldDivisor1` and is imported by `RiemannRoch_FunctionFieldDivisor3`.
--
--   **Formalization Note** The function field is not constructed from $k$: $K$ is an arbitrary field carrying the instances `Algebra k[X] K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, Mathlib's `FunctionField k K` (i.e. $K$ is finite-dimensional over $k(X)$) and `Algebra.IsSeparable k⟮X⟯ K`; when constants are needed, also `Algebra k K` with `IsScalarTower k k[X] K`. The norm is Mathlib's `Ideal.relNorm k[X] I`, prime factors with multiplicity are `UniqueFactorizationMonoid.normalizedFactors` (sums over multisets) and the inertia degree is `Ideal.inertiaDeg'`; the lemma is `FunctionField.Chart.finite_factorDegree_eq_relNorm`, deduced from the relative-norm identity of `RiemannRoch_Divisors`.
-- source:
--   H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 1.4 (degree of principal divisors, cf. Theorem 1.4.11 and its corollary); the identity itself is an auxiliary lemma of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/FunctionField/Divisor.lean

import Mathlib
import Definitions.Def_RiemannRoch_FunctionFieldDivisor1

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
theorem finite_factorDegree_eq_relNorm (I : Ideal (ringOfIntegers k K)) (hI : I ≠ ⊥) :
    ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
      Module.finrank k (k[X] ⧸ P.under k[X]) * (P.under k[X]).inertiaDeg' P).sum =
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.relNorm k[X] I)).map fun p =>
      Module.finrank k (k[X] ⧸ p)).sum := by
  let S := ringOfIntegers k K
  letI : Algebra k[X] (FractionRing S) := inferInstance
  letI : FaithfulSMul k[X] (FractionRing S) := inferInstance
  letI : Algebra (FractionRing k[X]) (FractionRing S) :=
    FractionRing.liftAlgebra k[X] (FractionRing S)
  letI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing S)
  letI : Algebra.IsSeparable (FractionRing k[X]) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv k[X] k⟮X⟯).symm.toRingEquiv
      (FractionRing.algEquiv S K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv k[X] k⟮X⟯).symm
      (FractionRing.algEquiv S K).symm x
  symm
  simpa only [Nat.mul_comm] using
    Ideal.sum_normalizedFactors_relNorm_of_isSeparable I hI
      (fun p : Ideal k[X] => Module.finrank k (k[X] ⧸ p))
end FunctionField.Chart
end
end
end


