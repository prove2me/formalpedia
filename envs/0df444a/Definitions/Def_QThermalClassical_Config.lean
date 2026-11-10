-- Prove2me | Definitions.Def_QThermalClassical_Config
-- name    : QThermalClassical_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:19.170935+00:00
-- url     : https://prove2.me/theorems/4be4d98e-983e-4279-931c-82b15daf3bb2
-- title:
--   Configurations $\chi$, $\sigma(\chi)$, validity and $u_S(X)$
-- statement:
--   A **configuration** (Definition 3.2) is an ordered list $\chi=((c_1,X_1),\dots,(c_l,X_l))$ of real coefficients and Hermitian monomials (with their term lists), and
--   $$
--   \sigma(\chi)=\bigotimes_{i=1}^l(I+c_iX_i)\qquad(82).
--   $$
--   It is **valid** (Lemma 11) if every $X_i$ is a Hermitian monomial and the monomials are disjoint (their supports (78) are pairwise disjoint). For unpinned sites $S$,
--   $$
--   u_S(X)=\{a\in\mathrm{unique}(C(X)) : a\cap S\neq\emptyset\}\qquad(84),
--   $$
--   $A(S)=\{a\in A: a\subseteq S\}$, and the invariant of Lemma 11 is $u_S(X_i)=\emptyset$ for $i\in[l-1]$.
--
--   **Formalization Note** On a valid configuration the factors act on disjoint qubits, so the tensor product (82) is the ordinary product, taken in list order.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 3.2, eq. (82), p.25; eq. (84), p.26; Lemma 11, p.29; p.19

import Mathlib
import Definitions.Def_QThermalClassical_IsHermitianMonomial
import Definitions.Def_QThermalClassical_IsConnectedSeq

set_option autoImplicit false

namespace QThermalClassical

/-- One entry `(c_i, X_i)` of a configuration, with the term list `C(X_i)` of its monomial. -/
structure Monomial (Q : Type) where
  /-- The real coefficient `c_i`. -/
  coeff : ℝ
  /-- The monomial `X_i`. -/
  op : Matrix (Q → Bool) (Q → Bool) ℂ
  /-- Its term list `C(X_i)`. -/
  terms : List (Q → Fin 4)

/-- A configuration `χ = {(c_1, X_1), …, (c_l, X_l)}` of Hermitian monomials (Definition 3.2),
as an ordered list. -/
abbrev Config (Q : Type) := List (Monomial Q)

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The operator `σ(χ) = ⊗_{i=1}^l (I + c_i X_i)` of eq. (82). The monomials of a valid
configuration act on disjoint sets of qubits, so the tensor product is the ordinary product,
taken in the order of the list. -/
def sigma (χ : Config Q) : Op Q :=
  (χ.map fun e => (1 : Op Q) + ((e.coeff : ℝ) : ℂ) • e.op).prod

/-- A valid configuration (Lemma 11, p.29): every `X_i` is a Hermitian monomial with term list
`C(X_i)`, and the monomials are disjoint, i.e. their supports (78) are pairwise disjoint.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 3.2, eq. (82), p.25; Lemma 11,
p.29. -/
def IsValidConfig (χ : Config Q) : Prop :=
  (∀ e ∈ χ, IsHermitianMonomial e.op e.terms) ∧
  χ.Pairwise fun e e' => Disjoint (wordsSupport e.terms) (wordsSupport e'.terms)

/-- `u_S(X) = {a ∈ unique(C(X)) : a ∩ S ≠ ∅}`, eq. (84), p.26: the distinct words of the term
list that meet the unpinned sites `S`. -/
def uSet (S : Finset Q) (C : List (PauliWord Q)) : Finset (PauliWord Q) :=
  C.toFinset.filter fun a => (pauliSupport a ∩ S).Nonempty

/-- `A(S) = {a ∈ A : a ⊆ S}` (p.19): the terms of `H` contained in `S`. -/
def termsIn (c : PauliWord Q → ℝ) (S : Finset Q) : Set (PauliWord Q) :=
  {a | c a ≠ 0 ∧ pauliSupport a ⊆ S}

/-- The invariant of Lemma 11: `u_S(X_i) = ∅` for every monomial but the last. -/
def PinInvariant (S : Finset Q) (χ : Config Q) : Prop :=
  ∀ e ∈ χ.dropLast, uSet S e.terms = ∅

end QThermalClassical


