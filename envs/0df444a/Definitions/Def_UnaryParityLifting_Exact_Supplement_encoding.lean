-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_encoding
-- name    : UnaryParityLifting_Exact_Supplement_encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:04.763689+00:00
-- url     : https://prove2.me/theorems/7b582630-d8b7-4e8a-942b-5ea3654b0681
-- title:
--   Fixed binary syntax charges
-- statement:
--   Fix a finite Boolean variable set V with a fixed enumeration. Variable names use b=max(1,ceil(log₂(|V|+1))) bits. Literal and end markers have two bits; an ordinary clause C has length 2+|C|(2+b). Natural-number fields use a unary payload-length prefix, a separator and the binary payload. Sparse parity equations list their nonzero variable coefficients and one right-hand-side bit; monomials list variable names and binary exponents. The empty monomial and empty clause have positive constant charge. Thus
--
--   $$|F|=\operatorname{bits}(|V|)+2+\sum_{C\in F}(2+|C|(2+b)).$$
--
--   This fixes the encoding charge used for size upper bounds and for both sides of reversible simulation. Coefficients are additionally charged by their unary magnitude using the published certificate size. No unbounded user-selected charge enters an upper bound. The enumeration is the canonical finite-type enumeration in Lean; only lengths, invariant under changing that enumeration, occur in these statements.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), pp.6–7, Definitions 2.2–2.3; p.20, Definition 7.1; p.25, after Theorem A.2

import Definitions.Def_UnaryParityLifting_Exact_certificateSyntax

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Fixed-width binary variable names, at least one bit. -/
def indexBits (V : Type) [Fintype V] : ℕ := max 1 (Nat.clog 2 (Fintype.card V + 1))
/-- A self-delimiting natural number: unary length, separator, binary payload. -/
def natBits (n : ℕ) : ℕ := 2 * max 1 (Nat.clog 2 (n + 1)) + 1
/-- Two-bit tags for literals/end-of-clause; each variable name has fixed width. -/
def clauseBits {V : Type} [Fintype V] (C : LiftSAParity.Clause V) : ℕ :=
  2 + C.card * (2 + indexBits V)
/-- Explicit sparse linear form, RHS bit and equation terminator. -/
def equationBits {V : Type} [Fintype V] (e : ParityEquation V) : ℕ :=
  3 + (Finset.univ.filter (fun v => e.coefficients v ≠ 0)).card * (2 + indexBits V)
def parityBits {V : Type} [Fintype V] (B : ParityClause V) : ℕ :=
  2 + (B.map equationBits).sum
def monomialBits {V : Type} [Fintype V] (d : V →₀ ℕ) : ℕ :=
  2 + ∑ v ∈ d.support, (2 + indexBits V + natBits (d v))
/-- Matched ordinary written-size convention, fixed rather than user supplied. -/
def binaryCharge (V : Type) [Fintype V] : EncodingCharge V where
  monomial := monomialBits
  ordinaryClause := clauseBits
  parityClause := parityBits
  monomial_pos := by intro d; unfold monomialBits; omega
  ordinaryClause_pos := by intro C; unfold clauseBits; omega
  parityClause_pos := by intro B; unfold parityBits; omega
/-- Header names the ambient variables, followed by explicit clause lists. -/
def cnfBits {V : Type} [Fintype V] (F : LiftSAParity.CNF V) : ℕ :=
  natBits (Fintype.card V) + 2 + ∑ C ∈ F, clauseBits C

end UnaryParityLifting.Exact.Supplement


