-- Prove2me | Definitions.Def_AvgCaseTI_gammaProb
-- name    : AvgCaseTI_gammaProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:30.676521+00:00
-- url     : https://prove2.me/theorems/9bf71ad9-0cbf-4f5b-a609-f8f378f4df8a
-- title:
--   Conditional probabilities $\gamma(n,q)$ and $\gamma^*(n,q)$
-- statement:
--   For a finite field $\mathbb F_q$ let $A$ be uniform in $\mathrm M(n,q)$ conditioned on $\mathrm{Tr}(A^2)=0$. Then
--   1. $\gamma(n,q)$ is the probability that $A$ has exactly one eigenvalue in $\mathbb F_q$, of algebraic multiplicity 1;
--   2. $\gamma^*(n,q)$ is the probability of the same event with the eigenvalue nonzero.
--
--   Both are ratios of counts: the matrices with $\mathrm{Tr}(A^2)=0$ and the spectral property, over all matrices with $\mathrm{Tr}(A^2)=0$ (a nonempty set, since it contains $0$).
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.11, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_AvgCaseTI_UniqueSimpleEig

set_option autoImplicit false

namespace AvgCaseTI

/-- **`γ(n, q)`: unique simple `F_q`-eigenvalue, conditioned on `Tr(A²) = 0`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.11, p.42
(PDF p.44): "Let γ(n, q) be the probability that a uniform matrix A ∈ M(n, q) conditioned on
Tr(A²) = 0 has exactly one eigenvalue in F_q, of algebraic multiplicity 1."

`gammaProb K n = |{A : Tr(A²) = 0, A ∈ C₁}| / |{A : Tr(A²) = 0}|`.

**Formalization Note.** The conditioning set contains `A = 0`, so the denominator is positive. -/
noncomputable def gammaProb (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : Mat K n // SelfDual A ∧ UniqueSimpleEig A} : ℝ) /
    Nat.card {A : Mat K n // SelfDual A}

/-- **`γ*(n, q)`**, Theorem 6.11, p.42 (PDF p.44): "the same conditional probability with the
additional requirement that the unique eigenvalue be nonzero". -/
noncomputable def gammaStarProb (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : Mat K n // SelfDual A ∧ UniqueSimpleNonzeroEig A} : ℝ) /
    Nat.card {A : Mat K n // SelfDual A}

end AvgCaseTI


