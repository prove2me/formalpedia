-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_certificateSyntax
-- name    : UnaryParityLifting_Exact_certificateSyntax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:20.705384+00:00
-- url     : https://prove2.me/theorems/ab44b4d6-6555-414f-9725-e4ac32e041a7
-- title:
--   Integer parity certificates and their charged written size
-- statement:
--   Let $V$ be a finite variable set. Ordinary clauses and CNFs are the referenced finite sets of signed literals and clauses. Source CNFs have no complementary pair in a clause. A width bound $w$ is positive; an empty clause is allowed. For an assignment $x$, $\overline C(x)$ is the indicator that every literal of $C$ fails.
--
--   A parity clause is a written list of equations $\sum_i a_i x_i=b$ over $\mathbb F_2$. Its falsification indicator is one precisely when all its equations fail, including one for the empty list. An integer parity certificate consists of integer polynomials $p_C$, with unrestricted natural monomial exponents, and a finite list of parity clauses $B_j$ with positive integer weights $\lambda_j$, satisfying
--   $$\sum_{C\in F}p_C(x)\overline C(x)=1+\sum_j\lambda_j\overline B_j(x)\quad(x\in\{0,1\}^V).$$
--
--   Its charged size is the sum of positive encoding charges for every written monomial and clause occurrence, plus $\sum_C\|p_C\|_{\mathrm{monomial},1}+\sum_j\lambda_j$. Each multiplier's identical monomials are collected; zero coefficients are absent from its support. The ordinary axiom occurrence is charged once for each nonzero multiplier. Each RHS clause occurrence is charged separately, without expanding its indicator. The encoding functions remain parameters because the source specifies no binary serialization. `HasParityCertificate` asserts existence of such data whose charged size is at most $S$.
--
--   The separate normalized data use nonnegative integer constant axiom coefficients; their validity, mass, and axiom support are defined without asserting that normalization is possible. This interface records Definition 2.3 without presupposing Lemma 2.4 or the lifting conclusion.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.6–8, Definitions 2.1–2.3, equations (2.1), (2.6)–(2.7), and the normalization proof

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace UnaryParityLifting.Exact

open scoped BigOperators

/-- Boolean bits as real numbers; source §2, pp.6–7. -/
def realBit (b : Bool) : ℝ := if b then 1 else 0

/-- Boolean bits as elements of F₂. -/
def fieldBit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- No complementary literals; repeated literals are already excluded by Finset. -/
def NoTautology {V : Type*} (C : LiftSAParity.Clause V) : Prop :=
  ∀ v, ¬ ((v, false) ∈ C ∧ (v, true) ∈ C)

def SourceCNF {V : Type*} (F : LiftSAParity.CNF V) : Prop :=
  ∀ C ∈ F, NoTautology C

/-- Positive upper bound on clause width; empty clauses are permitted. -/
def WidthAtMost {V : Type*} (F : LiftSAParity.CNF V) (w : ℕ) : Prop :=
  1 ≤ w ∧ SourceCNF F ∧ ∀ C ∈ F, C.card ≤ w

/-- Falsification, rather than satisfaction, is the barred clause function. -/
noncomputable def clauseIndicator {V : Type*} (C : LiftSAParity.Clause V)
    (x : V → Bool) : ℝ := by
  classical
  exact if LiftSAParity.Falsifies x C then 1 else 0

/-- The actual real polynomial (2.1), including the empty product 1. -/
noncomputable def clausePolynomial {V : Type*} (C : LiftSAParity.Clause V) :
    MvPolynomial V ℝ :=
  ∏ l ∈ C, if l.2 then 1 - MvPolynomial.X l.1 else MvPolynomial.X l.1

/-- One disjunct is the equation ∑ aᵢxᵢ = b over F₂ (Definition 2.1). -/
structure ParityEquation (V : Type*) where
  coefficients : V → ZMod 2
  rhs : ZMod 2

/-- Written equation occurrences, not an expanded indicator polynomial. -/
abbrev ParityClause (V : Type*) := List (ParityEquation V)

/-- Every disjunct must fail; the empty parity clause has indicator 1. -/
noncomputable def parityIndicator {V : Type*} [Fintype V] [DecidableEq V]
    (B : ParityClause V) (x : V → Bool) : ℝ := by
  classical
  exact if ∀ e ∈ B, (∑ v, e.coefficients v * fieldBit (x v)) ≠ e.rhs then 1 else 0

/-- A written nonzero RHS summand of (2.6). -/
structure ParitySummand (V : Type*) where
  clause : ParityClause V
  weight : ℕ
  weight_pos : 0 < weight

/-- Collected integer monomials may have arbitrary natural exponents. -/
structure CertificateSyntax {V : Type*} (F : LiftSAParity.CNF V) where
  multipliers : {C // C ∈ F} → MvPolynomial V ℤ
  nonnegativePart : List (ParitySummand V)

/-- The encoding is explicit and charges each written monomial and clause occurrence positively.
The source fixes no binary serialization (Definition 2.3, p.7). -/
structure EncodingCharge (V : Type*) where
  monomial : (V →₀ ℕ) → ℕ
  ordinaryClause : LiftSAParity.Clause V → ℕ
  parityClause : ParityClause V → ℕ
  monomial_pos : ∀ d, 0 < monomial d
  ordinaryClause_pos : ∀ C, 0 < ordinaryClause C
  parityClause_pos : ∀ B, 0 < parityClause B

/-- Unary monomial coefficient mass, never Fourier mass. -/
noncomputable def integerMonomialMass {V : Type*} (p : MvPolynomial V ℤ) : ℕ :=
  ∑ d ∈ p.support, (p.coeff d).natAbs

/-- Additive encoding lengths plus unary coefficient charge. Zero summands are omitted. -/
noncomputable def chargedSize {V : Type*} (enc : EncodingCharge V)
    {F : LiftSAParity.CNF V} (c : CertificateSyntax F) : ℕ := by
  classical
  exact (∑ C : {C // C ∈ F},
      ((if c.multipliers C = 0 then 0 else enc.ordinaryClause C.val) +
      (∑ d ∈ (c.multipliers C).support, enc.monomial d) +
      integerMonomialMass (c.multipliers C))) +
    (c.nonnegativePart.map (fun t => enc.parityClause t.clause + t.weight)).sum

/-- Definition 2.3: an identity on the entire Boolean cube, with integer input coefficients. -/
noncomputable def CertificateSyntax.Valid {V : Type*} [Fintype V] [DecidableEq V]
    {F : LiftSAParity.CNF V} (c : CertificateSyntax F) : Prop :=
  ∀ x : V → Bool,
    (∑ C : {C // C ∈ F},
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun v => realBit (x v)) (c.multipliers C) *
        clauseIndicator C.val x) =
      1 + (c.nonnegativePart.map (fun t => (t.weight : ℝ) * parityIndicator t.clause x)).sum

/-- S bounds the charged written size; includes the exactly-sized source instance.
No semantic proxy and no normalization hypothesis. -/
noncomputable def HasParityCertificate {V : Type*} [Fintype V] [DecidableEq V]
    (F : LiftSAParity.CNF V) (enc : EncodingCharge V) (S : ℕ) : Prop :=
  ∃ c : CertificateSyntax F, c.Valid ∧ chargedSize enc c ≤ S

/-- The data promised by normalization, not the input certificate. -/
structure NormalizedCertificate {V : Type*} (F : LiftSAParity.CNF V) where
  axiomCoefficient : {C // C ∈ F} → ℕ
  nonnegativePart : List (ParitySummand V)

noncomputable def NormalizedCertificate.Valid {V : Type*} [Fintype V] [DecidableEq V]
    {F : LiftSAParity.CNF V} (c : NormalizedCertificate F) : Prop :=
  ∀ x : V → Bool, (∑ C : {C // C ∈ F}, (c.axiomCoefficient C : ℝ) * clauseIndicator C.val x) =
    1 + (c.nonnegativePart.map (fun t => (t.weight : ℝ) * parityIndicator t.clause x)).sum

noncomputable def NormalizedCertificate.axiomMass {V : Type*}
    {F : LiftSAParity.CNF V} (c : NormalizedCertificate F) : ℕ :=
  ∑ C : {C // C ∈ F}, c.axiomCoefficient C

noncomputable def NormalizedCertificate.mass {V : Type*}
    {F : LiftSAParity.CNF V} (c : NormalizedCertificate F) : ℕ :=
  c.axiomMass + (c.nonnegativePart.map (fun t => t.weight)).sum

noncomputable def NormalizedCertificate.axiomSupport {V : Type*}
    {F : LiftSAParity.CNF V} (c : NormalizedCertificate F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun C => c.axiomCoefficient C ≠ 0)).card

end UnaryParityLifting.Exact


