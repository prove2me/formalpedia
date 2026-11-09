-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_Signs
-- name    : CommutativeRankNC_Approximation_Signs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:43.45356+00:00
-- url     : https://prove2.me/theorems/ce8ab643-3a7b-47ab-95c6-1e97af320d1f
-- title:
--   Finite-field seeds and unbiased sign laws
-- statement:
--   Set $r_f=\lceil\log_2\max(2,m)\rceil$ and $q=2^{r_f}$. Enumerate all monic degree-$r_f$ binary polynomials and take the first one with no monic divisor of degree between $1$ and $\lfloor r_f/2\rfloor$. Binary coefficient representatives implement addition, multiplication and inversion search modulo this polynomial. For a base-$q$ seed $a<q^t$, its digits specify $p_a(Z)=\sum_{j<t}a_jZ^j$. Define
--
--   $$\operatorname{Tr}(u)=\sum_{j<r_f}u^{2^j},\qquad \epsilon_i(a)=(-1)^{\operatorname{Tr}(p_a(\alpha_i))}.$$
--
--   Both arbitrary distinct points and the canonical first $m$ representatives are available. A trace bit of one denotes sign $-1$. The sign law is the pushforward of the uniform seed list, retaining repeated outputs; its support is the image of that list. For $m=1$ the resulting image is both signs with uniform law when $t>0$. Arbitrary finite sign laws and their at-most-$t$ joint unbiasedness are defined separately.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), §2.2, pp.9–11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Mathlib

noncomputable section

namespace CommutativeRankNC.Approximation

/-- Positive extension degree, with a two-element field for m≤1. -/
def fieldDegree (m : ℕ) : ℕ := Nat.clog 2 (max 2 m)
def fieldCard (m : ℕ) : ℕ := 2 ^ fieldDegree m

/-- The monic polynomial with the specified r low binary coefficients. -/
def binaryPolynomial (r a : ℕ) : Polynomial (ZMod 2) :=
  Polynomial.X ^ r + ∑ j ∈ Finset.range r,
    Polynomial.C (if a.testBit j then 1 else 0) * Polynomial.X ^ j

/-- Actual finite trial division test, as in the proof of Lemma 2.1. -/
def passesIrreducibilityTest (r a : ℕ) : Bool :=
  ((List.range (r / 2 + 1)).drop 1).all fun d =>
    (List.range (2 ^ d)).all fun b =>
      decide (binaryPolynomial r a %ₘ binaryPolynomial d b ≠ 0)

/-- First candidate in coefficient-bit order, from a finite search. The default
is relevant only if no irreducible candidate exists; its absence is theorem work. -/
def fieldPolynomialCode (m : ℕ) : ℕ :=
  ((List.range (fieldCard m)).find? (passesIrreducibilityTest (fieldDegree m))).getD 0

def fieldPolynomial (m : ℕ) : Polynomial (ZMod 2) :=
  binaryPolynomial (fieldDegree m) (fieldPolynomialCode m)

/-- Low-degree representative of a field element, encoded by its bits. -/
def fieldRepresentative (m a : ℕ) : Polynomial (ZMod 2) :=
  ∑ j ∈ Finset.range (fieldDegree m),
    Polynomial.C (if a.testBit j then 1 else 0) * Polynomial.X ^ j

def packField (m : ℕ) (p : Polynomial (ZMod 2)) : ℕ :=
  (∑ j ∈ Finset.range (fieldDegree m), (p.coeff j).val * 2 ^ j) % fieldCard m

def fieldAdd (m a b : ℕ) : ℕ :=
  packField m (fieldRepresentative m a + fieldRepresentative m b)

def fieldMul (m a b : ℕ) : ℕ :=
  packField m ((fieldRepresentative m a * fieldRepresentative m b) %ₘ fieldPolynomial m)

def fieldPow (m a : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => fieldMul m a (fieldPow m a d)

/-- Exhaustive inverse search; zero is totalized to zero. -/
def fieldInv (m a : ℕ) : ℕ :=
  ((List.range (fieldCard m)).find? (fun b => decide (fieldMul m a b = 1))).getD 0

def rawTrace (m a : ℕ) : ℕ :=
  ((List.range (fieldDegree m)).map (fun j => fieldPow m a (2 ^ j))).foldl (fieldAdd m) 0

/-- The trace is a bit, rather than a field-valued sign exponent. The trace
theorem establishes that rawTrace always equals 0 or 1 on field elements. -/
def traceBit (m a : ℕ) : Bool := decide (rawTrace m a = 1)

def seedCard (m t : ℕ) : ℕ := fieldCard m ^ t

/-- Seed digits are the coefficients of the degree <t polynomial. -/
def seedCoefficient (m a j : ℕ) : ℕ := (a / fieldCard m ^ j) % fieldCard m

def seedEvaluation (m t a i : ℕ) : ℕ :=
  ((List.range t).map (fun j =>
    fieldMul m (seedCoefficient m a j) (fieldPow m i j))).foldl (fieldAdd m) 0

abbrev SignVector (m : ℕ) := Fin m → Bool

def signSeed (m t a : ℕ) : SignVector m :=
  fun i => traceBit m (seedEvaluation m t a i.val)

def signSeedAt (m t : ℕ) (α : Fin m → ℕ) (a : ℕ) : SignVector m :=
  fun i => traceBit m (seedEvaluation m t a (α i))

def signWeightAt (m t : ℕ) (α : Fin m → ℕ) (e : SignVector m) : ℝ :=
  ((List.range (seedCard m t)).countP (fun a => decide (signSeedAt m t α a = e)) : ℝ) /
    (seedCard m t : ℝ)

def signList (m t : ℕ) : List (SignVector m) :=
  (List.range (seedCard m t)).map (signSeed m t)

def signSupport (m t : ℕ) : Finset (SignVector m) := (signList m t).toFinset

/-- Pushforward of the uniform SEED law; duplicated signs retain multiplicity. -/
def signWeight (m t : ℕ) (e : SignVector m) : ℝ :=
  ((List.range (seedCard m t)).countP (fun a => decide (signSeed m t a = e)) : ℝ) /
    (seedCard m t : ℝ)

def signValue (b : Bool) : ℚ := if b then -1 else 1

/-- Arbitrary finite laws, including nonuniform weights on their support. -/
def IsSignLaw {m : ℕ} (p : SignVector m → ℝ) : Prop :=
  (∀ e, 0 ≤ p e) ∧ ∑ e, p e = 1

def TWiseUnbiased {m : ℕ} (t : ℕ) (p : SignVector m → ℝ) : Prop :=
  IsSignLaw p ∧ ∀ (s : ℕ), s ≤ t → ∀ (I : Fin s ↪ Fin m) (δ : Fin s → Bool),
    ∑ e : SignVector m, (if (∀ j, e (I j) = δ j) then p e else 0) = (2 : ℝ) ^ (-(s : ℤ))

end CommutativeRankNC.Approximation


