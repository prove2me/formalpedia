-- Prove2me | Definitions.Def_DerivationHitting_Commutative_PolynomialData
-- name    : DerivationHitting_Commutative_PolynomialData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:26.627803+00:00
-- url     : https://prove2.me/theorems/a73d886c-6660-45f4-a42d-37fe0b6aa386
-- title:
--   Ordinary derivative space and the explicit logarithmic generator
-- statement:
--   Let $F$ be a field, let $n,r\in\mathbb N$, and let $f\in F[x_1,\ldots,x_n]$. For each finite sequence of variable indices, take the corresponding ordinary iterated partial derivative of $f$, with the empty sequence returning $f$. Write $V_f$ for the $F$-linear span of all these derivatives, and say that $f$ has bounded partials at $r$ when $\dim_F V_f\le r$.
--
--   Set $B=nr^2+r$. For $1\le i\le n$, define
--   $$
--    a_{i,0}=0,\qquad a_{i,k}=\frac{(-1)^{k-1}i^k}{k}\quad(k\ge1),\qquad
--    G_i(t)=\sum_{k=0}^{B}a_{i,k}t^k,\qquad P_i(t)=\sum_{k\ge0}a_{i,k}t^k.
--   $$
--   The two substitution maps send $x_i$ to $G_i\in F[t]$ and $P_i\in F[[t]]$, respectively. A finite family is derivative-closed when its $F$-linear span contains each first partial derivative of each member.
--
--   These definitions give the input class and the exact generator of Theorem 1.1, and the formal logarithms of Theorem 4.1. Their intended use assumes characteristic zero, so every positive integer denominator is nonzero. No topology or analytic logarithm is involved.
--
--   **Formalization Note** Variables use $\operatorname{Fin}(n)$ with index shifted by one. Dimension is cardinal rank, so an infinite-dimensional space cannot satisfy a finite bound through a default value. The sum includes degree $B$ and is zero at $r=0$.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 3, §1, Theorem 1.1 and following displayed construction; p. 15, Theorem 4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Mathlib

namespace DerivationHitting.Commutative
noncomputable section

/-- Ordinary iterated partial derivatives; the empty sequence gives the input polynomial. -/
def iteratedPartial {F : Type*} [Field F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) (w : List (Fin n)) : MvPolynomial (Fin n) F :=
  w.foldl (fun g i => MvPolynomial.pderiv i g) f

/-- The span of all ordinary iterated partial derivatives, including order zero. -/
def partialSpace {F : Type*} [Field F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) : Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F (Set.range (iteratedPartial f))

/-- Cardinal dimension avoids a finite-rank default on an infinite-dimensional space. -/
def hasBoundedPartials {F : Type*} [Field F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) (r : ℕ) : Prop :=
  Module.rank F (partialSpace f) ≤ (r : Cardinal)

/-- The cutoff used in Theorems 1.1 and 4.1. -/
def cutoff (n r : ℕ) : ℕ := n * r ^ 2 + r

/-- `i : Fin n` denotes the source variable numbered `i.val + 1`. -/
def logarithmCoefficient {F : Type*} [Field F] {n : ℕ}
    (i : Fin n) (k : ℕ) : F :=
  if k = 0 then 0 else (-1 : F) ^ (k - 1) * ((i.val + 1 : ℕ) : F) ^ k / (k : F)

/-- The finite generator includes the term of degree `cutoff n r`. -/
def generator {F : Type*} [Field F] (n r : ℕ) (i : Fin n) : Polynomial F :=
  ∑ k ∈ Finset.range (cutoff n r + 1),
    Polynomial.monomial k (logarithmCoefficient i k)

/-- Substitution is an actual polynomial algebra homomorphism. -/
def polynomialSubstitution {F : Type*} [Field F] (n r : ℕ) :
    MvPolynomial (Fin n) F →ₐ[F] Polynomial F :=
  MvPolynomial.aeval (generator n r)

/-- Formal zero-constant logarithm, without any analytic or topological interpretation. -/
def formalLogarithm {F : Type*} [Field F] {n : ℕ} (i : Fin n) : PowerSeries F :=
  PowerSeries.mk (logarithmCoefficient i)

/-- Polynomial substitution into the formal logarithms. -/
def logarithmSubstitution {F : Type*} [Field F] (n : ℕ) :
    MvPolynomial (Fin n) F →ₐ[F] PowerSeries F :=
  MvPolynomial.aeval formalLogarithm

/-- Derivative-closed means the span of the family is stable under each partial derivative. -/
def derivativeClosed {F : Type*} [Field F] {n q : ℕ}
    (g : Fin q → MvPolynomial (Fin n) F) : Prop :=
  ∀ i j, MvPolynomial.pderiv i (g j) ∈ Submodule.span F (Set.range g)

end
end DerivationHitting.Commutative


