-- Prove2me | Definitions.Def_RSCapacity_AffineGeometry
-- name    : RSCapacity_AffineGeometry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:56.289201+00:00
-- url     : https://prove2.me/theorems/e7c2859a-3cc4-4a26-bd02-9c07310fea5c
-- title:
--   Affine algebraic sets, dimension, Heintz degree and cumulative degree
-- statement:
--   All sets live in affine space $\mathbb A^N=K^N$ over a field $K$ (algebraically closed in the theorems).
--
--   1. An **affine algebraic set** is the common zero set $Z(S)$ of a set $S$ of polynomials. The **Zariski closure** of $V$ is $Z(I(V))$, where $I(V)$ is the ideal of polynomials vanishing on $V$.
--   2. The **dimension** of $V$ is the Krull dimension of $K[x_1,\dots,x_N]/I(V)$ (it is $-\infty$ for the empty set).
--   3. The **degree** of an irreducible variety $V$ of dimension $s$ is the degree of its projective closure, read through Heintz's characterization: the largest number of points of $V\cap E$ over affine linear subspaces $E$ of codimension $s$ with $V\cap E$ finite.
--   4. The **cumulative degree** $\operatorname{cdeg}(V)$ is the sum of the degrees of the irreducible components of the closure of $V$.
--   5. A **constructible** set is a finite union of sets $Z(I)\cap\{g\neq0\}$; its dimension and cumulative degree are those of its Zariski closure.
--   6. A point $x$ is **isolated** in $Z$ when some basic open set $\{g\neq0\}$ meets $Z$ exactly in $x$.
--   7. The graph of a rational map $\phi=(N_1/H^{e_1},\dots,N_N/H^{e_N})$ on $U\subseteq\mathbb A^m$ is $\{(u,\phi(u)):u\in U\}\subseteq\mathbb A^{m+N}$, and $p\in K^{d+1}$ is the coefficient vector of $P_p(X)=\sum_{j=0}^dp_jX^j$.
--
--   These notions carry the geometric half of the mission: a bounded-degree, low-dimensional cover of the solution locus of a differential equation.
--
--   **Formalization Note** The degree is Heintz's (J. Heintz, *Definability and fast quantifier elimination in algebraically closed fields*, Theoret. Comput. Sci. 24 (1983), Definition 1 and Remark 2), valued in `ℕ∞`; $E$ is cut out by $s$ affine equations with linearly independent linear parts. Components are the zero sets of the minimal primes of $I(V)$ (finitely many). Because `algDim` and `cdeg` are computed from $I(V)$, they are those of the Zariski closure for every set.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §6.2, p.24 (PDF 26); Lemma 6.4, p.24; §6.3, p.25 (PDF 27); Lemma 7.2, p.29 (PDF 31)

import Mathlib

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-!
# Affine algebraic sets, dimension, degree and cumulative degree

Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §6.2, p.24
(PDF 26): "All algebraic varieties in the proof are considered over an algebraic closure. The
degree of an affine irreducible variety means the degree of its projective closure. If V is an
affine algebraic set with irreducible components V_1, …, V_t, define its cumulative degree by
cdeg(V) := ∑_{j=1}^{t} deg(V_j)." Also Lemma 6.4, p.24 (constructible sets, graphs of rational
maps), Lemma 7.2, p.29 (isolated points) and §6.3, p.25 (coefficient vectors).

**Formalization Note.**
* Affine N-space over K is `Fin N → K`. `zeroSet S` is the common zero set of a set of
  polynomials; an algebraic set is a `zeroSet`; `zClosure V` is the Zariski closure
  Z(I(V)) (Mathlib `zeroLocus`/`vanishingIdeal`).
* `algDim V` is the Krull dimension of K[x_1, …, x_N]/I(V) (`ringKrullDim`, valued in
  `WithBot ℕ∞`; the empty set has dimension `⊥`). The irreducible components of the closure of V
  are the zero sets of the minimal primes of I(V).
* The degree of an irreducible affine variety V of dimension s (`heintzDeg`) is Heintz's
  characterization of the degree of its projective closure (J. Heintz, *Definability and fast
  quantifier elimination in algebraically closed fields*, Theoret. Comput. Sci. 24 (1983),
  Definition 1 and Remark 2): the supremum of |V ∩ E| over affine linear subspaces E of
  codimension s with V ∩ E finite. E is the solution set of s affine linear equations with
  linearly independent linear parts. The value is in ℕ∞.
* `cdeg V` sums `heintzDeg` over the irreducible components of the closure of V. Because I(V) is
  the ideal of the closure, `algDim V` and `cdeg V` of any set are those of its Zariski closure;
  this is how the dimension and cumulative degree of a constructible set are read (Lemma 6.4).
* A constructible set is a finite union of locally closed sets Z(I) ∩ {g ≠ 0}.
* A point p = (p_0, …, p_d) ∈ K^{d+1} is the coefficient vector of P_p(X) = ∑ p_j X^j (p.25,
  `polyOfVec`).
* `cdeg` is a finite sum (`finsum`): I(V) has finitely many minimal primes (K[x] is Noetherian).
* x is an isolated point of Z when some basic open set {g ≠ 0} meets Z exactly in x (Zariski
  topology).
-/

open MvPolynomial

/-- The common zero set of a set of polynomials. -/
def zeroSet {K : Type*} [Field K] {N : ℕ} (S : Set (MvPolynomial (Fin N) K)) : Set (Fin N → K) :=
  {x | ∀ f ∈ S, eval x f = 0}

/-- V is an affine algebraic set. -/
def IsAlgSet {K : Type*} [Field K] {N : ℕ} (V : Set (Fin N → K)) : Prop :=
  ∃ S : Set (MvPolynomial (Fin N) K), V = zeroSet S

/-- The Zariski closure Z(I(V)). -/
def zClosure {K : Type*} [Field K] {N : ℕ} (V : Set (Fin N → K)) : Set (Fin N → K) :=
  zeroLocus K (vanishingIdeal K V)

/-- The dimension of (the Zariski closure of) V: the Krull dimension of K[x]/I(V). -/
noncomputable def algDim {K : Type*} [Field K] {N : ℕ} (V : Set (Fin N → K)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial (Fin N) K ⧸ vanishingIdeal K V)

/-- The affine linear subspace {x : ∑_j a_{ij} x_j = b_i for all i}. -/
def affSub {K : Type*} [Field K] {N s : ℕ} (a : Matrix (Fin s) (Fin N) K) (b : Fin s → K) :
    Set (Fin N → K) :=
  {x | ∀ i, ∑ j, a i j * x j = b i}

/-- Heintz's degree of an irreducible affine variety V of dimension s: the supremum of |V ∩ E|
over affine linear subspaces E of codimension s with V ∩ E finite. -/
noncomputable def heintzDeg {K : Type*} [Field K] {N : ℕ} (V : Set (Fin N → K)) : ℕ∞ :=
  ⨆ (s : ℕ) (_ : algDim V = ((s : ℕ∞) : WithBot ℕ∞)) (a : Matrix (Fin s) (Fin N) K)
    (b : Fin s → K) (_ : LinearIndependent K fun i => a i) (_ : (V ∩ affSub a b).Finite),
    ((V ∩ affSub a b).ncard : ℕ∞)

/-- The cumulative degree: the sum of the degrees of the irreducible components of the Zariski
closure of V. -/
noncomputable def cdeg {K : Type*} [Field K] {N : ℕ} (V : Set (Fin N → K)) : ℕ∞ :=
  ∑ᶠ 𝔭 ∈ (vanishingIdeal K V : Ideal (MvPolynomial (Fin N) K)).minimalPrimes,
    heintzDeg (zeroLocus K 𝔭 : Set (Fin N → K))

/-- U is constructible: a finite union of sets Z(I_j) ∩ {g_j ≠ 0}. -/
def IsConstructible {K : Type*} [Field K] {N : ℕ} (U : Set (Fin N → K)) : Prop :=
  ∃ (t : ℕ) (I : Fin t → Set (MvPolynomial (Fin N) K)) (g : Fin t → MvPolynomial (Fin N) K),
    U = ⋃ j, zeroSet (I j) ∩ {x | eval x (g j) ≠ 0}

/-- x is an isolated point of Z in the Zariski topology. -/
def IsIsolatedIn {K : Type*} [Field K] {N : ℕ} (x : Fin N → K) (Z : Set (Fin N → K)) : Prop :=
  x ∈ Z ∧ ∃ g : MvPolynomial (Fin N) K, eval x g ≠ 0 ∧ ∀ y ∈ Z, eval y g ≠ 0 → y = x

/-- The graph {(u, ϕ(u)) : u ∈ U} ⊆ 𝔸^{m+N} of ϕ = (N_1/H^{e_1}, …, N_N/H^{e_N}). -/
noncomputable def ratGraph {K : Type*} [Field K] {m N : ℕ} (U : Set (Fin m → K))
    (H : MvPolynomial (Fin m) K) (Nf : Fin N → MvPolynomial (Fin m) K) (e : Fin N → ℕ) :
    Set (Fin (m + N) → K) :=
  {x | ∃ u ∈ U, x = Fin.append u (fun j => eval u (Nf j) / eval u H ^ e j)}

/-- The polynomial P_p(X) = ∑_{j=0}^{d} p_j X^j with coefficient vector p = (p_0, …, p_d) ∈ K^{d+1}
(p.25). -/
noncomputable def polyOfVec {K : Type*} [Field K] {d : ℕ} (p : Fin (d + 1) → K) : K[X] :=
  ∑ j : Fin (d + 1), Polynomial.C (p j) * Polynomial.X ^ (j : ℕ)

end RSCapacity


