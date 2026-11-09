-- Prove2me | Definitions.Def_NCFactorClosure607_Circuits_Polynomials
-- name    : NCFactorClosure607_Circuits_Polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:33.80986+00:00
-- url     : https://prove2.me/theorems/89428a22-d9ee-46c8-9f37-740d2772de3f
-- title:
--   Noncommutative polynomials: word coefficients $[w]P$, monomials and degree
-- statement:
--   Let $F$ be a field and $X$ a set of noncommuting variables. Write $X^*$ for the free monoid of finite words over $X$, with empty word $\varepsilon$, and $F\langle X\rangle$ for the free associative algebra: its elements are finite $F$-linear combinations of words, multiplied by concatenation, so that
--   $$[w](PQ)=\sum_{uv=w}[u]P\,[v]Q .$$
--
--   This file fixes the basic vocabulary used throughout the mission.
--
--   1. The **coefficient** $[w]P\in F$ of a word $w$ in a polynomial $P$, read through the identification of $F\langle X\rangle$ with the monoid algebra of $X^*$.
--   2. The **monomial** of a word $w=x_{i_1}\cdots x_{i_k}$, the product $x_{i_1}\cdots x_{i_k}\in F\langle X\rangle$ (the empty product $1$ for $w=\varepsilon$).
--   3. The **degree** $\deg P$: the maximum length of a word with nonzero coefficient.
--   4. The predicate "$P$ has degree at most $D$": every word with nonzero coefficient in $P$ has length at most $D$. This concerns the polynomial itself, not any circuit computing it.
--
--   **Formalization Note** Polynomials are Mathlib's `FreeAlgebra F X`, words are `FreeMonoid X`, and coefficients are read off through `FreeAlgebra.equivMonoidAlgebraFreeMonoid`. The degree of the zero polynomial is set to $0$; the source defines degree only for nonzero polynomials and every statement of the mission uses it only for nonzero ones.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.4–5, §2 (eq. (1) and the definition of degree); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib

/-!
# Noncommutative polynomials: coefficients, words, degree

Arvind–Joglekar, *Factor Closure in Noncommutative Algebraic Complexity*,
STOC 2027 submission #607, §2, p.4–5.

Polynomials in noncommuting variables `X` over a field `F` are elements of Mathlib's free
algebra `FreeAlgebra F X` (= `F⟨X⟩`). Words are elements of `FreeMonoid X` (= `X*`).
-/

namespace NCFactorClosure607.Circuits

/-- The coefficient family of a noncommutative polynomial: the finitely supported function
`w ↦ [w]P` on words, read off through Mathlib's identification of `F⟨X⟩` with the monoid
algebra of the free monoid `X*`. -/
noncomputable def coeffs {F : Type*} [Field F] {X : Type*} (P : FreeAlgebra F X) :
    FreeMonoid X →₀ F :=
  (FreeAlgebra.equivMonoidAlgebraFreeMonoid P).coeff

/-- `coeff w P` is the coefficient `[w]P` of the word `w` in the polynomial `P` (§2, p.4). -/
noncomputable def coeff {F : Type*} [Field F] {X : Type*} (w : FreeMonoid X)
    (P : FreeAlgebra F X) : F :=
  coeffs P w

/-- The monomial of a word: `wordPoly w = x_{i₁} ⋯ x_{i_k}` for `w = x_{i₁} ⋯ x_{i_k}`,
and `wordPoly ε = 1`. -/
noncomputable def wordPoly {F : Type*} [Field F] {X : Type*} (w : FreeMonoid X) :
    FreeAlgebra F X :=
  (w.toList.map (FreeAlgebra.ι F)).prod

/-- The degree of a polynomial: the maximum length of a word with nonzero coefficient
(§2, p.5). For `P = 0` the value is `0` by convention; every use in the mission has `P ≠ 0`. -/
noncomputable def ncDeg {F : Type*} [Field F] {X : Type*} (P : FreeAlgebra F X) : ℕ :=
  (coeffs P).support.sup (fun w => w.toList.length)

/-- `DegLE P D`: the polynomial `P` has degree at most `D`, i.e. every word with nonzero
coefficient in `P` has length at most `D`. This is about the polynomial, not about any
circuit computing it. -/
def DegLE {F : Type*} [Field F] {X : Type*} (P : FreeAlgebra F X) (D : ℕ) : Prop :=
  ∀ w : FreeMonoid X, coeff w P ≠ 0 → w.toList.length ≤ D

end NCFactorClosure607.Circuits


