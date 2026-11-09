-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_BooleanAlgebra
-- name    : RandomCNFDeficiency_LowerBound_BooleanAlgebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:35.959873+00:00
-- url     : https://prove2.me/theorems/4e0f25bc-c32f-48ff-943d-4db990226532
-- title:
--   Boolean polynomial algebra and irreducible normal forms
-- statement:
--   Let $K$ be any field and $B=K[x_1,\ldots,x_n]/\langle x_i^2-x_i\rangle$. Represent $B$ by functions from the Boolean cube to $K$, with pointwise algebra operations. The unique multilinear coefficient of $x_S$ is given explicitly by
--
--   $$[x_S]f=\sum_{T\subseteq S}(-1)^{|S|-|T|}f(1_T).$$
--
--   The degree is the largest $|S|$ with nonzero coefficient, with degree of zero set to zero; variables are the union of those supports. Fix degree-lex with $x_{n-1}>\cdots>x_0$. A monomial is reducible modulo an ideal $J$ exactly when it is the largest nonzero monomial of some member of $J$. A normal form of $f$ is supported on irreducible monomials and congruent to $f$ modulo $J$. The total operation $R_J(f)$ chooses such a form when one exists and otherwise returns zero. Existence, uniqueness, linearity and all reduction identities remain the separate Lemma 2.1 obligation. Ordinary polynomial evaluation defines multilinearization.
--
--   This explicit function-algebra realization is isomorphic to the stated quotient over every field, including characteristic two. The coefficient formula is its inverse multilinear interpolation; no target properties are bundled into a structure.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 2.1, definitions before Lemma 2.1, printed p. 6, PDF p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Mathlib
set_option autoImplicit false
open scoped BigOperators

namespace RandomCNFDeficiency.LowerBound

/-- Coordinate-function realization of K[x]/(x_i²-x_i), with pointwise multiplication.
The coefficients below are the explicit Boolean Möbius transform, over every field. -/
abbrev BooleanAlgebra (n : ℕ) (K : Type*) := (Fin n → Bool) → K

noncomputable def cubePoint {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ T)

noncomputable def booleanCoeff {n : ℕ} {K : Type*} [Field K]
    (f : BooleanAlgebra n K) (S : Finset (Fin n)) : K :=
  ∑ T ∈ S.powerset, (-1 : K) ^ (S.card - T.card) * f (cubePoint T)

noncomputable def booleanSupport {n : ℕ} {K : Type*} [Field K]
    (f : BooleanAlgebra n K) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun S => booleanCoeff f S ≠ 0

noncomputable def booleanDegree {n : ℕ} {K : Type*} [Field K]
    (f : BooleanAlgebra n K) : ℕ := (booleanSupport f).sup Finset.card

noncomputable def booleanVars {n : ℕ} {K : Type*} [Field K]
    (f : BooleanAlgebra n K) : Finset (Fin n) := (booleanSupport f).biUnion id

def booleanMonomial {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n)) : BooleanAlgebra n K :=
  fun a => ∏ i ∈ S, if a i then (1 : K) else 0

/-- Increasing rank implements degree-lex, with x_(n-1) > ... > x_0. -/
def monomialRank {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  2 ^ n * S.card + ∑ i ∈ S, 2 ^ i.val

def Reducible {n : ℕ} {K : Type*} [Field K]
    (J : Ideal (BooleanAlgebra n K)) (S : Finset (Fin n)) : Prop :=
  ∃ q ∈ J, booleanCoeff q S ≠ 0 ∧
    ∀ T, booleanCoeff q T ≠ 0 → monomialRank T ≤ monomialRank S

def IsNormalForm {n : ℕ} {K : Type*} [Field K]
    (J : Ideal (BooleanAlgebra n K)) (f r : BooleanAlgebra n K) : Prop :=
  (∀ S, booleanCoeff r S ≠ 0 → ¬ Reducible J S) ∧ f - r ∈ J

/-- Total choice of an irreducible representative. Existence and uniqueness are
NOT assumed: they are conclusions of Lemma 2.1. Outside that existence predicate
this returns zero, a branch Lemma 2.1 proves is never taken. -/
noncomputable def reduction {n : ℕ} {K : Type*} [Field K]
    (J : Ideal (BooleanAlgebra n K)) (f : BooleanAlgebra n K) : BooleanAlgebra n K := by
  classical
  exact if h : ∃ r, IsNormalForm J f r then Classical.choose h else 0

/-- Actual evaluation of an ordinary polynomial on the Boolean cube. -/
noncomputable def multilinearize {n : ℕ} {K : Type*} [Field K]
    (p : MvPolynomial (Fin n) K) : BooleanAlgebra n K :=
  fun a => MvPolynomial.eval (fun i => if a i then (1 : K) else 0) p

end RandomCNFDeficiency.LowerBound


