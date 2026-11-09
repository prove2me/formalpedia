-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_DigitEncoding
-- name    : AlmostLinearModComp_Composition_DigitEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:57.470307+00:00
-- url     : https://prove2.me/theorems/41a8e10e-9aa5-4ec9-997b-c6212cf1b86f
-- title:
--   Power-of-two digits and the weighted deformation
-- statement:
--   Choose $m\ge1$ positive integers $k_i$, and put $d_i=2^{k_i}$, $N=\prod_i d_i$, $w_i=\prod_{j<i}d_j$, and $\alpha_i(e)=\lfloor e/w_i\rfloor\bmod d_i$. Let
--   $$L=1+\sum_i(d_i-1),\qquad F=X^{N-n}f,\qquad b_i=a^{w_i}\operatorname{rem}F.$$
--   The constructed targets are $a_i=X^{w_i}+tb_i$. The encoded outer polynomial is
--   $$P(z)=\sum_{e<n}g_e t^{L-1-\sum_i\alpha_i(e)}z^{\alpha(e)}.$$
--
--   The definition substitutes these targets into $P$, reduces each coefficient of $t$ modulo the monic $F$, and truncates at $t^L$. It uses a polynomial in $t$ with coefficients in $R[X]$ as a canonical representative of the double quotient. The digit bounds, modulus and targets are computed from the input data; no arbitrary optimum, basis or target is supplied. These are semantic polynomial definitions, not free arithmetic-circuit gates.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §2, equations (1)–(2), printed p.3 / PDF p.4; Lemma 2.1, printed p.4 / PDF p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Mathlib

open scoped BigOperators

noncomputable section

namespace AlmostLinearModComp.Composition

/-- Section 2 power-of-two radices, stored by their positive binary exponents. -/
structure Radices where
  m : ℕ
  positive_m : 0 < m
  exponent : Fin m → ℕ
  positive_exponent : ∀ i, 0 < exponent i

def Radices.digitBound (d : Radices) (i : Fin d.m) : ℕ := 2 ^ d.exponent i

def Radices.size (d : Radices) : ℕ := ∏ i, d.digitBound i

def Radices.weight (d : Radices) (i : Fin d.m) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin d.m => j < i), d.digitBound j

def Radices.digit (d : Radices) (e : ℕ) (i : Fin d.m) : ℕ :=
  e / d.weight i % d.digitBound i

def Radices.multiIndex (d : Radices) (e : ℕ) : Fin d.m →₀ ℕ :=
  Finsupp.onFinset Finset.univ (d.digit e) (by intros; simp)

def Radices.totalDigit (d : Radices) (e : ℕ) : ℕ := ∑ i, d.digit e i

def Radices.precision (d : Radices) : ℕ := 1 + ∑ i, (d.digitBound i - 1)

def paddedSize (n : ℕ) : ℕ := 2 ^ Nat.clog 2 n

def paddedModulus {R : Type*} [CommRing R] (n : ℕ) (d : Radices)
    (f : Polynomial R) : Polynomial R := Polynomial.X ^ (d.size - n) * f

/-- Coefficientwise canonical reduction in X, with t as the outer polynomial variable.
This is a mathematical representative map, never a circuit primitive. -/
def reduceX {R : Type*} [CommRing R] (F : Polynomial R)
    (p : Polynomial (Polynomial R)) : Polynomial (Polynomial R) :=
  ∑ k ∈ p.support, Polynomial.monomial k (p.coeff k %ₘ F)

/-- Canonical t-truncation; valid precision is supplied by the statements. -/
def truncateT {R : Type*} [CommRing R] (L : ℕ)
    (p : Polynomial (Polynomial R)) : Polynomial (Polynomial R) :=
  ∑ k ∈ Finset.range L, Polynomial.monomial k (p.coeff k)

/-- The b_i are constructed from a, rather than supplied as unrelated targets. -/
def powerTarget {R : Type*} [CommRing R] (d : Radices)
    (F a : Polynomial R) (i : Fin d.m) : Polynomial R :=
  a ^ d.weight i %ₘ F

/-- Equation (1): outer variable t, coefficient variable X. -/
def deformedTarget {R : Type*} [CommRing R] (d : Radices)
    (F a : Polynomial R) (i : Fin d.m) : Polynomial (Polynomial R) :=
  Polynomial.C (Polynomial.X ^ d.weight i) +
    Polynomial.X * Polynomial.C (powerTarget d F a i)

/-- Equation (2): coefficients lie in R[t], with the exact balancing power of t. -/
def encodedOuter {R : Type*} [CommRing R] (n : ℕ) (d : Radices)
    (g : Polynomial R) : MvPolynomial (Fin d.m) (Polynomial R) :=
  ∑ e ∈ Finset.range n, MvPolynomial.monomial (d.multiIndex e)
    (Polynomial.monomial (d.precision - 1 - d.totalDigit e) (g.coeff e))

/-- Substitute the genuine deformed targets and select the canonical representative
in (R[X]/(F))[t]/(t^L). All reduction steps have explicit finite bodies. -/
def encodedEvaluation {R : Type*} [CommRing R] (n : ℕ) (d : Radices)
    (F a g : Polynomial R) : Polynomial (Polynomial R) :=
  truncateT d.precision (reduceX F
    (MvPolynomial.eval₂Hom
      (Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R))
      (deformedTarget d F a) (encodedOuter n d g)))

end AlmostLinearModComp.Composition


