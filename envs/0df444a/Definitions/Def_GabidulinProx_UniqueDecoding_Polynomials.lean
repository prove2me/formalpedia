-- Prove2me | Definitions.Def_GabidulinProx_UniqueDecoding_Polynomials
-- name    : GabidulinProx_UniqueDecoding_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:16.237698+00:00
-- url     : https://prove2.me/theorems/9c9c394f-6968-4d4a-823a-b830d759f851
-- title:
--   Linearized polynomials, specialization, interpolation and annihilators
-- statement:
--   For a natural number $q$ and coefficients $c_i$ in a commutative semiring, the coefficient family represents the actual polynomial
--
--   $$f(X)=\sum_{i<k}c_iX^{q^i}.$$
--
--   Membership in $\mathcal L(q,m,k)$ means having such a representation; the unrestricted class is the union over $k$. At $k=0$ it contains only zero. In finite-field uses $q=|K|$, where $K$ is the base field and $L$ its finite extension. Composition is the ordinary polynomial composition operation, used as the symbolic product.
--
--   The module defines evaluation on an ordered list of points, specialization of $Z$ in a coefficient family, and evaluation of $X$ while leaving $Z$ formal. For a finite parameter set $S$, the ordinary Lagrange interpolant is constructed explicitly from its nodal product formula. Each $p_j$ interpolates the coefficient of $X^{q^j}$ in a given decoded family. The empty-set interpolant is zero and the empty nodal product is one.
--
--   For a $K$-subspace $W\le L$, the annihilator is
--
--   $$A_W(X)=\prod_{w\in W}(X-w).$$
--
--   These are polynomial objects, so their coefficients, divisibility, and composition are available independently of evaluation as functions. No existence lemma is used to choose a polynomial.
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), §2.1 pp.11–12; Lemma 2.7 p.14; §3.2 pp.19–22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Mathlib

open scoped BigOperators

namespace GabidulinProx.UniqueDecoding

/-- §2.1, p.11: an actual polynomial, not a polynomial function. -/
noncomputable def linearized {R : Type*} [CommSemiring R] (q : ℕ) {k : ℕ}
    (c : Fin k → R) : Polynomial R :=
  ∑ i, Polynomial.monomial (q ^ i.val) (c i)

/-- Membership in L(q,m,k), including the zero polynomial. At k=0 only zero belongs. -/
def IsLinearized {R : Type*} [CommSemiring R] (q k : ℕ) (f : Polynomial R) : Prop :=
  ∃ c : Fin k → R, f = linearized q c

/-- The unbounded class L(q,m); q-degree bounds are expressed by IsLinearized. -/
def IsQPolynomial {R : Type*} [CommSemiring R] (q : ℕ) (f : Polynomial R) : Prop :=
  ∃ k : ℕ, IsLinearized q k f

/-- Evaluation of the coefficient family; q is |K| in all finite-field theorems. -/
def qeval {R : Type*} [CommSemiring R] (q : ℕ) {k : ℕ}
    (c : Fin k → R) (x : R) : R := ∑ i, c i * x ^ (q ^ i.val)

/-- Evaluation at the ordered independent points A. -/
def evaluateWord {L : Type*} [Semiring L] {n : ℕ}
    (α : Fin n → L) (f : Polynomial L) : Fin n → L := fun r => f.eval (α r)

/-- §3.2 p.21: specialize Z in a family of X-coefficients. -/
noncomputable def specialize {L : Type*} [CommSemiring L] (q : ℕ) {k : ℕ}
    (a : Fin k → Polynomial L) (z : L) : Polynomial L :=
  linearized q (fun i => (a i).eval z)

/-- Evaluate X, leaving the second variable Z formal. -/
noncomputable def familyEval {L : Type*} [CommSemiring L] (q : ℕ) {k : ℕ}
    (a : Fin k → Polynomial L) (x : L) : Polynomial L :=
  ∑ i, a i * Polynomial.C (x ^ (q ^ i.val))

/-- Product ∏(Z-z), equal to 1 for an empty set. -/
noncomputable def rootProduct {L : Type*} [Field L] (S : Finset L) : Polynomial L :=
  ∏ z ∈ S, (Polynomial.X - Polynomial.C z)

/-- The ordinary Lagrange interpolant on S, with empty-set value zero. -/
noncomputable def lagrange {L : Type*} [Field L] (S : Finset L) (c : L → L) : Polynomial L := by
  classical
  exact ∑ z ∈ S, Polynomial.C (c z / ∏ w ∈ S.erase z, (z - w)) *
    ∏ w ∈ S.erase z, (Polynomial.X - Polynomial.C w)

/-- The p_j of §3.2 p.21 are constructed from the decoded polynomial coefficients. -/
noncomputable def coefficientInterpolants {L : Type*} [Field L] (q k : ℕ)
    (S : Finset L) (Pz : L → Polynomial L) : Fin k → Polynomial L :=
  fun j => lagrange S (fun z => (Pz z).coeff (q ^ j.val))

/-- The monic subspace annihilator ∏_{w∈W}(X-w), pp.14,19. -/
noncomputable def annihilator (K : Type*) {L : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype L] (W : Submodule K L) : Polynomial L := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  exact ∏ w : W, (Polynomial.X - Polynomial.C (w : L))

end GabidulinProx.UniqueDecoding


