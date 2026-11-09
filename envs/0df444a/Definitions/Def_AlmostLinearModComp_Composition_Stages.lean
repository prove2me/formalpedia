-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_Stages
-- name    : AlmostLinearModComp_Composition_Stages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:38.935983+00:00
-- url     : https://prove2.me/theorems/2b50f6e0-8a65-437d-8487-552cfb23af32
-- title:
--   Halving stages, canonical arrays and coordinate specifications
-- statement:
--   Positive binary radix exponents define exactly the power-of-two radices of Section 2. A stage selects a digit and a strictly smaller exponent for its new bound. Its other bounds are the original radices below that digit and one above it; the last coordinate records powers of $X^v$. Old and new vectors both have $N$ coordinates ordered by their exponent at $t=0$.
--
--   The finite array has side $3s_j$ at the halved digit and $2s_i$ at every other digit, including the extra coordinate. Mixed-radix weights, digits, range size, and the increasing list of stages are explicit integer computations. Canonical arrays are the highest $X$ coefficients of the genuine basis products after reduction modulo $F$ and truncation in $t$.
--
--   The matrices $E_v$ and $T_{2v}$ are semantic specifications. The inverse of $E_v$ is represented modulo $t^L$ by its finite nilpotent geometric series; these matrices are never inputs to the circuit routines. Arbitrary compatible targets and arbitrary individually degree-bounded polynomials are serialized by all their relevant coefficients. The common soft bound is $CNLb(1+\log_2(NL+2))^k$, with the displayed factor $b=2^m$ or $4^m$ outside the logarithm.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), §§2–3.2, printed pp.3–6 / PDF pp.4–7; Proposition 4.1, printed p.8 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_DigitEncoding

open scoped BigOperators

namespace AlmostLinearModComp.Composition

/-- One of the actual halvings. Bounds below j are unchanged; bounds above j are one. -/
structure Stage (d : Radices) where
  j : Fin d.m
  halvedExponent : ℕ
  exponent_lt : halvedExponent < d.exponent j

def Stage.bound {d : Radices} (s : Stage d) (i : Fin d.m) : ℕ :=
  if i < s.j then d.digitBound i else if i = s.j then 2 ^ s.halvedExponent else 1

def Stage.v {d : Radices} (s : Stage d) : ℕ := d.weight s.j * 2 ^ s.halvedExponent

def Stage.sides {d : Radices} (s : Stage d) (i : ℕ) : ℕ :=
  if h : i < d.m then s.bound ⟨i, h⟩ else d.size / s.v

def Stage.arraySide {d : Radices} (s : Stage d) (i : ℕ) : ℕ :=
  (if i = s.j.val then 3 else 2) * s.sides i

def Stage.arrayWeight {d : Radices} (s : Stage d) (i : ℕ) : ℕ :=
  ((List.range i).map s.arraySide).prod

def Stage.arraySize {d : Radices} (s : Stage d) : ℕ := s.arrayWeight (d.m + 1)

def Stage.arrayDigit {d : Radices} (s : Stage d) (e i : ℕ) : ℕ :=
  e / s.arrayWeight i % s.arraySide i

/-- Old and new coefficient vectors are both ordered by their exponent at t=0. -/
def Stage.basisDigit {d : Radices} (s : Stage d) (old : Bool) (e i : ℕ) : ℕ :=
  if hi : i < d.m then
    e / d.weight ⟨i, hi⟩ % ((if old && i = s.j.val then 2 else 1) * s.sides i)
  else e / ((if old then 2 else 1) * s.v)

def Stage.arrayIndex {d : Radices} (s : Stage d) (a : ℕ → ℕ) : ℕ :=
  ((List.range (d.m + 1)).map fun i => s.arrayWeight i * a i).sum

/-- Increasing preparation order v=1,2,...,N/2. Reversal is the evaluation order. -/
def allStages (d : Radices) : List (Stage d) :=
  (List.finRange d.m).flatMap fun j =>
    (List.finRange (d.exponent j)).map fun h => ⟨j, h.val, h.isLt⟩

noncomputable section

/-- Semantic specification only: t is outer, and each coefficient is reduced modulo F. -/
def basisElement {R : Type*} [CommRing R] (F : Polynomial R) (L v : ℕ)
    {m : ℕ} (a : Fin m → Polynomial (Polynomial R)) (gamma : ℕ → ℕ) :
    Polynomial (Polynomial R) :=
  truncateT L (reduceX F
    (Polynomial.C (Polynomial.X ^ (v * gamma m)) * ∏ i, a i ^ gamma i.val))

def stageBasis {R : Type*} [CommRing R] {d : Radices} (s : Stage d)
    (F : Polynomial R) (L : ℕ) (a : Fin d.m → Polynomial (Polynomial R))
    (old : Bool) : Matrix (Fin d.size) (Fin d.size) (Polynomial R) :=
  fun i e => ∑ t ∈ Finset.range L, Polynomial.monomial t
    (((basisElement F L ((if old then 2 else 1) * s.v) a
      (s.basisDigit old e)).coeff t).coeff i)

/-- E_v inverse by the finite nilpotent geometric series. This dense matrix is a
mathematical specification and is never supplied to the circuit builder. -/
def coordinateMatrix {R : Type*} [CommRing R] {d : Radices} (s : Stage d)
    (F : Polynomial R) (L : ℕ) (a : Fin d.m → Polynomial (Polynomial R)) :
    Matrix (Fin d.size) (Fin d.size) (Polynomial R) :=
  (∑ h ∈ Finset.range L, (1 - stageBasis s F L a false) ^ h) * stageBasis s F L a true

/-- Exactly equation (6), in array-major, then t-coefficient order. -/
def canonicalArray {R : Type*} [CommRing R] {d : Radices} (s : Stage d)
    (F : Polynomial R) (L : ℕ) (a : Fin d.m → Polynomial (Polynomial R)) : List R :=
  ((List.range s.arraySize).map fun e => (List.range L).map fun t =>
    ((basisElement F L s.v a (s.arrayDigit e)).coeff t).coeff (d.size - 1)).flatten

/-- The full input domain of Proposition 4.1, without a balancing or deformation restriction. -/
def CompatibleTargets {R : Type*} [CommRing R] (d : Radices)
    (a : Fin d.m → Polynomial (Polynomial R)) : Prop :=
  ∀ i, (a i).coeff 0 = Polynomial.X ^ d.weight i

/-- Canonical coefficient vector of arbitrary P evaluated at arbitrary compatible targets. -/
def evaluationVector {R : Type*} [CommRing R] (d : Radices) (L : ℕ)
    (F : Polynomial R) (a : Fin d.m → Polynomial (Polynomial R))
    (P : MvPolynomial (Fin d.m) (Polynomial R)) : List R :=
  let value := truncateT L (reduceX F (MvPolynomial.eval₂Hom
    (Polynomial.mapRingHom (Polynomial.C : R →+* Polynomial R)) a P))
  ((List.range d.size).map fun i => (List.range L).map fun t =>
    (value.coeff t).coeff i).flatten

/-- Coefficient-array serialization preserves arbitrary t representatives by reading their jets. -/
def targetVector {R : Type*} [CommRing R] (d : Radices) (L : ℕ)
    (a : Fin d.m → Polynomial (Polynomial R)) : List R :=
  ((List.finRange d.m).map fun j => ((List.range d.size).map fun i =>
    (List.range L).map fun t => ((a j).coeff t).coeff i).flatten).flatten

def outerVector {R : Type*} [CommRing R] (d : Radices) (L : ℕ)
    (P : MvPolynomial (Fin d.m) (Polynomial R)) : List R :=
  ((List.range d.size).map fun e => (List.range L).map fun t =>
    (P.coeff (d.multiIndex e)).coeff t).flatten

/-- All stored/target t-coefficients are canonical degree-<N X representatives. -/
def CanonicalTargets {R : Type*} [CommRing R] (d : Radices) (L : ℕ)
    (a : Fin d.m → Polynomial (Polynomial R)) : Prop :=
  ∀ i t, t < L → ((a i).coeff t).degree < (d.size : WithBot ℕ)

/-- Uniform soft bound: the displayed exponential in m stays outside the logarithm. -/
def evaluationBound (C : ℝ) (k N L factor : ℕ) : ℝ :=
  C * N * L * factor * (1 + Real.logb 2 (N * L + 2)) ^ k

end
end AlmostLinearModComp.Composition


