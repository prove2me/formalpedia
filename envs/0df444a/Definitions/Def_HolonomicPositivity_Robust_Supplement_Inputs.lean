-- Prove2me | Definitions.Def_HolonomicPositivity_Robust_Supplement_Inputs
-- name    : HolonomicPositivity_Robust_Supplement_Inputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:54:10.822221+00:00
-- url     : https://prove2.me/theorems/3c4708b6-2f18-41f6-a35d-e286aa14f7b7
-- title:
--   Finite algebraic coefficient and initial-value descriptions for partial recursive procedures
-- statement:
--   A real algebraic number is represented by the published integer polynomial and rational isolating interval description, with its published denotation relation. Its raw data are explicitly equivalent to $\operatorname{List}(\mathbb Z)\times\mathbb Q\times\mathbb Q$, providing a primitive recursive encoding.
--
--   A rational-function description is a pair of lists of algebraic-number descriptions, with coefficients in increasing degree order. It denotes $P\in\mathbb R(x)$ when the lists denote real polynomials $A,B$ with $B\ne0$ and
--   $$P=A/B.$$
--   No reduction or canonical description is required. Raw invalid descriptions have no denotation. A coefficient input describes $(P,Q)$; a positivity input adds descriptions of the three initial values; a certificate output describes $(S,L)$ and a natural starting index $N$.
--
--   The list and product encodings make all three data types primitive codable. Mathlib's partial recursive functions over these concrete encodings express an actual algorithm. The denotation relations constrain only which mathematical data the finite syntax names, and impose no extra mathematical restriction on real algebraic inputs.
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; PDF p.2 (XX:2), lines 57-58; p.7 (XX:7), Theorem 3.6 input; pp.8-10 (XX:8-10), Procedure 1 and Lemma 5.2. Encoding implements the finite inputs; the AlgNum denotation is reused from PolygonPack_AlgNum.

import Mathlib
import Definitions.Def_PolygonPack_AlgNum

namespace HolonomicPositivity.Robust.Supplement

/-- Explicit finite encoding of the published algebraic-number descriptions by integer
lists and rational interval endpoints. No validity condition is imposed on raw syntax. -/
def algNumEquiv : PolygonPack.AlgNum ≃ (List ℤ × ℚ × ℚ) where
  toFun a := (a.coeffs, a.lo, a.hi)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

instance algNumPrimcodable : Primcodable PolygonPack.AlgNum :=
  Primcodable.ofEquiv (List ℤ × ℚ × ℚ) algNumEquiv

/-- A rational-function description: numerator and denominator coefficient lists, low degree
first. Denotation below requires a nonzero denominator. Inputs are algebraic (PDF p.2). -/
abbrev RatDesc := List PolygonPack.AlgNum × List PolygonPack.AlgNum

/-- The actual polynomial represented by a real coefficient list. -/
noncomputable def realPolyOf : List ℝ → Polynomial ℝ
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * realPolyOf cs

/-- A finite description denotes P if its coefficients denote those of an actual numerator
and nonzero denominator, and their quotient is P. All descriptions, including nonreduced
ones and trailing zeros, are accepted by the algorithmic theorems. -/
def RatDenotes (d : RatDesc) (P : RatFunc ℝ) : Prop :=
  ∃ a b : List ℝ,
    List.Forall₂ PolygonPack.AlgNum.Denotes d.1 a ∧
    List.Forall₂ PolygonPack.AlgNum.Denotes d.2 b ∧ realPolyOf b ≠ 0 ∧
    P = algebraMap (Polynomial ℝ) (RatFunc ℝ) (realPolyOf a) /
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (realPolyOf b)

/-- Descriptions of a pair of recurrence coefficients. -/
abbrev CoeffInput := RatDesc × RatDesc

/-- The input of the positivity procedure: P,Q and three algebraic initial values. -/
abbrev Input := CoeffInput × (PolygonPack.AlgNum × PolygonPack.AlgNum × PolygonPack.AlgNum)

/-- The output of the certificate algorithm: S,L and the starting index N. -/
abbrev CertOutput := (RatDesc × RatDesc) × ℕ

/-- The coefficient descriptions name P and Q. -/
def CoeffDenotes (d : CoeffInput) (P Q : RatFunc ℝ) : Prop :=
  RatDenotes d.1 P ∧ RatDenotes d.2 Q

/-- The three descriptions name v₀,v₁,v₂. -/
def InitialDenotes (d : PolygonPack.AlgNum × PolygonPack.AlgNum × PolygonPack.AlgNum)
    (v : Fin 3 → ℝ) : Prop :=
  d.1.Denotes (v 0) ∧ d.2.1.Denotes (v 1) ∧ d.2.2.Denotes (v 2)

end HolonomicPositivity.Robust.Supplement


