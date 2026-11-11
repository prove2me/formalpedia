-- Prove2me | Definitions.Def_JinMaoSubsetSum_IsTermList
-- name    : JinMaoSubsetSum_IsTermList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:12.16759+00:00
-- url     : https://prove2.me/theorems/842626ef-7ef8-4998-b736-242ba4a567fe
-- title:
--   Sparse polynomials with nonnegative coefficients as lists of nonzero terms
-- statement:
--   Lemma 3.1 multiplies polynomials $f(x),g(x)$ with coefficients in $\mathbb Z\cap[0,U]$, represented as lists of nonzero terms. A list of pairs $(e,c)$ represents $f$ when it contains every term $c\,x^e$ of $f$ with $c\neq0$ exactly once, in any order. The output of the multiplication lists the nonzero terms of $h=fg$ in increasing order of degree.
--
--   **Formalization Note** Polynomials are `Polynomial ℕ`. `IsTermList l f` is the representation predicate, `termsSorted h` the nonzero terms of $h$ by increasing degree, and `termWords l` the integers written for a term list (its length, then $e_1,c_1,e_2,c_2,\dots$).
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Lemma 3.1, p.15 (PDF p.17)

import Mathlib

set_option autoImplicit false

namespace JinMaoSubsetSum

/-!
# Sparse polynomials as lists of nonzero terms

Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, §3.2, Lemma 3.1, p.15:
"Given polynomials f(x), g(x) (represented as lists of nonzero terms) with degrees at most N and
all coefficients in ℤ ∩ [0, U] [...]".

**Formalization Note.**
* A polynomial with coefficients in `ℤ ∩ [0, U]` is a `Polynomial ℕ`.
* `IsTermList l f`: `l` lists every nonzero term of `f` exactly once, as (degree, coefficient)
  pairs, in any order.
* `termsSorted h` is the list of nonzero terms of `h` in increasing order of degree (the output
  order fixed by this formalization); `termWords l` is the number of terms followed by
  `e_1, c_1, e_2, c_2, …`.
-/

/-- `l` lists the nonzero terms `(e, c)` of `f`, each degree once, in any order. -/
def IsTermList (l : List (ℕ × ℕ)) (f : Polynomial ℕ) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ p ∈ l, p.2 ≠ 0 ∧ f.coeff p.1 = p.2) ∧
    ∀ e, f.coeff e ≠ 0 → ∃ p ∈ l, p.1 = e

/-- The nonzero terms of `h`, in increasing order of degree. -/
noncomputable def termsSorted (h : Polynomial ℕ) : List (ℕ × ℕ) :=
  (h.support.sort (· ≤ ·)).map (fun e => (e, h.coeff e))

/-- Memory layout of a term list: the number of terms, then `e_1, c_1, e_2, c_2, …`. -/
def termWords (l : List (ℕ × ℕ)) : List ℤ :=
  (l.length : ℤ) :: l.flatMap (fun p => [(p.1 : ℤ), (p.2 : ℤ)])

end JinMaoSubsetSum


