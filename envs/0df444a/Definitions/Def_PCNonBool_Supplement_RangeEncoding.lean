-- Prove2me | Definitions.Def_PCNonBool_Supplement_RangeEncoding
-- name    : PCNonBool_Supplement_RangeEncoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:28:30.333909+00:00
-- url     : https://prove2.me/theorems/270e3425-4f7b-4fbf-8b7b-c339cb0ce547
-- title:
--   Range-polynomial encoding $P_{c,\mathcal L}$ of linear inequalities
-- statement:
--   Fix a field $\mathbb F$ and $c\in\mathbb F\setminus\{0\}$, and use $\{1,c\}$-valued variables $y_1,\dots,y_n$ with intended meaning $y_i=c^{x_i}$. For an inequality $L:\ \sum_i a_ix_i+\sum_i\bar a_i\bar x_i\ge b$ let $\|\ell\|=\sum_i a_i+\sum_i\bar a_i$, let
--   $$\mathrm{Sat}(L)=\{a\in\mathbb N : b\le a\le\|\ell\|\}$$
--   be the values of the left-hand side that satisfy $L$, and let $m_1=\prod_i y_i^{a_i}$, $\bar m_2=\prod_i y_i^{\bar a_i}$, $d_2=\sum_i\bar a_i$. The **range polynomial** of $L$ is
--   $$p_L=\prod_{a\in\mathrm{Sat}(L)}\bigl(c^{d_2}m_1-c^{a}\bar m_2\bigr).$$
--   Without negative literals this is $\prod_{a\in\mathrm{Sat}(L)}(m_\ell-c^a)$ with $m_\ell=\prod_i y_i^{a_i}$. The set $P_{c,\mathcal L}$ consists of the range polynomials of the inequalities in $\mathcal L$ together with the range axioms $(y_i-1)(y_i-c)$, $i\in[n]$.
--
--   When $c$ is not a root of unity, a point of $\{1,c\}^n$ is a common zero of $P_{c,\mathcal L}$ exactly when it encodes a $0/1$ solution of $\mathcal L$. This is the encoding of Theorem 8.1.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (97)–(98), p.58 (PDF p.61); Remark 8.5, p.62 (PDF p.65)

import Mathlib
import Definitions.Def_PCNonBool_Supplement_CuttingPlanes

namespace PCNonBool.Supplement

open MvPolynomial

/-- `Sat(L) = [b, ‖ℓ‖]`, the values in the a priori range of `ℓ` that satisfy `L : ℓ ≥ b`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (97), p.58 (PDF p.61)), as a set of natural numbers. -/
def Ineq.sat {n : ℕ} (L : Ineq n) : Finset ℕ :=
  (Finset.range (L.norm + 1)).filter (fun a => L.rhs ≤ (a : ℤ))

/-- The range polynomial of the inequality `L : ∑ a_i x_i + ∑ ā_i x̄_i ≥ b` over `{1, c}`-valued
variables `y_i` (intended `y_i = c^{x_i}`) (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (98), p.58 (PDF p.61), in the dual-free form
of Remark 8.5, p.62 (PDF p.65)):
`p'_L = ∏_{a ∈ Sat(L)} (c^{d₂} m₁ - c^a m̄₂)`, with `m₁ = ∏ y_i^{a_i}`, `m̄₂ = ∏ y_i^{ā_i}` and
`d₂ = ∑ ā_i`. Without negative literals (`ā = 0`) it is (98)'s `p_L = ∏_{a ∈ Sat(L)} (m_ℓ - c^a)`. -/
noncomputable def rangePoly {F : Type*} [Field F] (c : F) {n : ℕ} (L : Ineq n) :
    MvPolynomial (Fin n) F :=
  ∏ a ∈ L.sat, (C (c ^ (∑ i, L.neg i)) * ∏ i, X i ^ L.pos i - C (c ^ a) * ∏ i, X i ^ L.neg i)

/-- `P_{c,L}` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.58 (PDF p.61)): the range polynomials of the inequalities in `Ls`, in the
variables `y_1, …, y_n`, together with the range axioms `(y_i - 1)(y_i - c)` for all `i`. -/
noncomputable def rangeAxioms {F : Type*} [Field F] (c : F) {n : ℕ} (Ls : List (Ineq n)) :
    Set (MvPolynomial (Fin n) F) :=
  {p | (∃ L ∈ Ls, p = rangePoly c L) ∨ (∃ i : Fin n, p = (X i - 1) * (X i - C c))}

end PCNonBool.Supplement


