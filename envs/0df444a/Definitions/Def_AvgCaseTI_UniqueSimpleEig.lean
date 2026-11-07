-- Prove2me | Definitions.Def_AvgCaseTI_UniqueSimpleEig
-- name    : AvgCaseTI_UniqueSimpleEig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:25.285779+00:00
-- url     : https://prove2.me/theorems/64dfd331-b29d-46ee-87b0-b6de1a6552bc
-- title:
--   Unique simple $\mathbb F_q$-eigenvalue, eigenvalue-free matrices, left eigenspaces
-- statement:
--   Let $A\in\mathrm M(n,\mathbb F)$ with characteristic polynomial $c_A(t)$. The **eigenvalues of $A$ in $\mathbb F$** are the roots of $c_A$ in $\mathbb F$, and the **algebraic multiplicity** of a root is its multiplicity as a root of $c_A$.
--   1. $A$ has **exactly one eigenvalue in $\mathbb F$, of algebraic multiplicity 1** if $c_A(t)=(t-\lambda)f_0(t)$ with $f_0$ having no root in $\mathbb F$; i.e. $c_A$ has exactly one root $\lambda\in\mathbb F$ and it is simple.
--   2. The same with $\lambda\neq0$.
--   3. $A$ is **eigenvalue-free** if $c_A$ has no root in $\mathbb F$.
--   4. The **left eigenspace** of $A$ for $\lambda$ is $\{v\in\mathbb F^{1\times n}: vA=\lambda v\}$.
--
--   These spectral conditions select the hull generator in the algorithm of Theorem 1.1, and their probabilities are the random-matrix results of §6.
--
--   **Formalization Note** Roots are taken of `Matrix.charpoly A` in `K` and multiplicities are `Polynomial.rootMultiplicity` (algebraic, not geometric, multiplicity; no roots outside $\mathbb F$). Row vectors are `Fin n → K` with `Matrix.vecMul`.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §6.1, pp.35–37 (PDF pp.37–39); Theorem 3.5, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

variable {K : Type*} [Field K] {n : ℕ}

/-- **Exactly one eigenvalue in `F_q`, of algebraic multiplicity 1.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), §6.1, pp.35–36
(PDF pp.37–38): "C₁(n, q) := {A ∈ M(n, q) : A has only 1 eigenvalue in F_q with algebraic
multiplicity 1}", i.e. `c_A(t) = (t − λ) f₀(t)` with `f₀` free of roots in `F_q`.

`UniqueSimpleEig A`: the characteristic polynomial of `A` has exactly one root `a` in `K`, and
`a` is a simple root.

**Formalization Note.** Eigenvalues in `F_q` are the roots in `K` of `Matrix.charpoly A`; algebraic
multiplicity is `Polynomial.rootMultiplicity`. -/
def UniqueSimpleEig (A : Mat K n) : Prop :=
  ∃ a : K, A.charpoly.IsRoot a ∧ A.charpoly.rootMultiplicity a = 1 ∧
    ∀ b : K, A.charpoly.IsRoot b → b = a

/-- **Exactly one eigenvalue in `F_q`, nonzero and of algebraic multiplicity 1**, Corollary 6.4,
p.37 (PDF p.39), Theorem 3.5, p.18 (PDF p.20): `C*₁(n, q)`. -/
def UniqueSimpleNonzeroEig (A : Mat K n) : Prop :=
  ∃ a : K, a ≠ 0 ∧ A.charpoly.IsRoot a ∧ A.charpoly.rootMultiplicity a = 1 ∧
    ∀ b : K, A.charpoly.IsRoot b → b = a

/-- **Eigenvalue-free matrices**, §6.1, p.35 (PDF p.37): the characteristic polynomial has no root
in `F_q`. -/
def EigenvalueFree (A : Mat K n) : Prop := ∀ a : K, ¬ A.charpoly.IsRoot a

/-- **The left eigenspace** `{v ∈ F_q^{1×n} | v A = a v}` of `A` for `a` (row vectors, `vecMul`),
§3.1, pp.18–19 (PDF pp.20–21). -/
def leftEigenspace (A : Mat K n) (a : K) : Submodule K (Fin n → K) :=
  LinearMap.ker (Matrix.vecMulLinear A - a • LinearMap.id)

end AvgCaseTI


