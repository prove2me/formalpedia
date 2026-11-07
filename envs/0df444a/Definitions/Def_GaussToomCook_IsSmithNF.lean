-- Prove2me | Definitions.Def_GaussToomCook_IsSmithNF
-- name    : GaussToomCook_IsSmithNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:16.481676+00:00
-- url     : https://prove2.me/theorems/aa16f8f8-3677-432d-b83c-6c136446b4c8
-- title:
--   Smith normal form with divisibility chain; counts and prefix products of elementary divisors
-- statement:
--   Let $R$ be a commutative ring and $A$ an $n\times n$ matrix over $R$. A **Smith normal form** of $A$ is a factorization
--   $$U\,A\,V=\operatorname{diag}(d_0,\dots,d_{n-1}),\qquad d_0\mid d_1\mid\cdots\mid d_{n-1},$$
--   with $U,V$ square matrices of unit determinant. Over a principal ideal domain one exists and the $d_i$ are unique up to units; $d_{i-1}$ is the $i$-th **elementary divisor** $e_i$ of $A$, and for a matrix expressing a basis of a lattice $L$ in a basis of $M\supseteq L$ they are the elementary divisors of $L\subseteq M$.
--
--   Two derived quantities are defined: the number of $d_i$ divisible by $p$ ("the number of elementary divisors divisible by $p$"), and the product of the first $i$ of them, $e_1\cdots e_i=d_0\cdots d_{i-1}$ (equal to $1$ for $i=0$).
--
--   **Formalization Note** The divisibility chain is part of the definition: Mathlib's `Basis.SmithNormalForm` does not carry it, and the products and counts of eqs. (91), (94) depend on it.
-- source:
--   Y. Spiizer, R. S. Steiner, Rational and Gaussian long integer multiplication, manuscript (STOC 2027 submission; held version sha256 f50b53628a53a03bd55785424af241d0ac5ea751714330838e4017b90b27ad70), §9.3, proof of Proposition 9.5, p. 31 (PDF p. 33), and Lemma 9.6, p. 32 (PDF p. 34)

import Mathlib

namespace GaussToomCook

/-- **Elementary divisors via a Smith normal form**, Spiizer, Steiner, *Rational and Gaussian long integer multiplication*, manuscript (STOC 2027 submission; sha256 f50b5362…27ad70), §9.3, proof of
Proposition 9.5, p. 31 (PDF 33): "Let e₁ | e₂ | ⋯ | e_{2k−1} be the elementary divisors of V(S)".

`IsSmithNF A U V d` says that `U` and `V` are invertible (unit determinant), `U * A * V` is the diagonal
matrix with diagonal `d`, and `d 0 ∣ d 1 ∣ ⋯` (`d i ∣ d j` whenever `i ≤ j`). Over a principal ideal domain
such a form exists and `d` is unique up to units; `d i` is the `(i+1)`-st elementary divisor `e_{i+1}`.

**Formalization Note.** Mathlib's `Basis.SmithNormalForm` carries no divisibility chain, which the
products and counts of (91), (94) and Propositions 9.4, 9.5 depend on, so the chain is part of this
definition. Statements are made for every Smith form, which equals "the" elementary divisors up to units. -/
def IsSmithNF {R : Type*} [CommRing R] {n : ℕ} (A U V : Matrix (Fin n) (Fin n) R)
    (d : Fin n → R) : Prop :=
  IsUnit U.det ∧ IsUnit V.det ∧ U * A * V = Matrix.diagonal d ∧
    ∀ i j : Fin n, i ≤ j → d i ∣ d j

/-- The number of entries of `d` divisible by `p`: "the number of elementary divisors … divisible by p"
(Propositions 9.4, 9.5, p. 31). -/
noncomputable def pdvdCount {R : Type*} [CommRing R] {n : ℕ} (p : R) (d : Fin n → R) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => p ∣ d i)).card

/-- The product of the first `i` entries of `d`, `e₁ ⋯ e_i` (eqs. (91), (94), pp. 31–32); for `i ≥ n`
it is the product of all entries, and for `i = 0` it is `1`. -/
def prefixProd {R : Type*} [CommRing R] {n : ℕ} (d : Fin n → R) (i : ℕ) : R :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < i), d j

end GaussToomCook


