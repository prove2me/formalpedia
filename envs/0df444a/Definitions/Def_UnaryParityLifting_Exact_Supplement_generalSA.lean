-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_generalSA
-- name    : UnaryParityLifting_Exact_Supplement_generalSA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:44:41.467298+00:00
-- url     : https://prove2.me/theorems/f1512707-e791-47f6-bf1b-c0bf81153c5d
-- title:
--   General formal real SA certificates
-- statement:
--   For a finite CNF F, let C̄ be its published clause polynomial and let t range over distinct consistent conjunctions of literals. General real Sherali–Adams data consists of arbitrary real polynomials p_C,r_i and collected nonnegative weights α_t. Validity is the formal polynomial identity
--
--   $$\sum_{C\in F}p_C\bar C+\sum_i r_i(x_i^2-x_i)=1+\sum_t\alpha_t t.$$
--
--   A degree threshold d bounds deg(p_C)+|C|, deg(r_i)+2 and deg(t) for every nonzero summand before cancellation. A large coefficient is an actual nonzero monomial coefficient of a multiplier or a collected conical weight whose absolute value is at least the given threshold. This model contains no hardness assumption and includes signed, nonconstant multipliers and explicit Boolean axioms. It supplies the universal certificate domain of Theorem 5.1.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), pp.6–7, Definition 2.2 and equation (2.4); p.18, §5.2 preamble

import Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- General real formal SA data (2.4); no sign restriction on p or r. -/
structure GeneralSA {V : Type} (F : LiftSAParity.CNF V) where
  multiplier : {C // C ∈ F} → MvPolynomial V ℝ
  booleanMultiplier : V → MvPolynomial V ℝ
  conical : ConicalRepresentation V

def GeneralSA.Valid {V : Type} [Fintype V] {F : LiftSAParity.CNF V}
    (q : GeneralSA F) : Prop :=
  (∑ C : {C // C ∈ F}, q.multiplier C * clausePolynomial C.val) +
    (∑ i : V, q.booleanMultiplier i * (MvPolynomial.X i ^ 2 - MvPolynomial.X i)) =
      1 + q.conical.polynomial
/-- Before cancellation; zero summands do not contribute. Real degree threshold. -/
def GeneralSA.DegreeLE {V : Type} [Fintype V] {F : LiftSAParity.CNF V}
    (q : GeneralSA F) (d : ℝ) : Prop :=
  (∀ C, q.multiplier C ≠ 0 → ((q.multiplier C).totalDegree + C.val.card : ℕ) ≤ d) ∧
  (∀ i, q.booleanMultiplier i ≠ 0 → ((q.booleanMultiplier i).totalDegree + 2 : ℕ) ≤ d) ∧
  (∀ t, q.conical.coefficient t ≠ 0 → (termDegree t : ℝ) ≤ d)
/-- An actual collected coefficient, not a mass or an artificially split list. -/
def GeneralSA.HasLargeCoefficient {V : Type} [Fintype V] {F : LiftSAParity.CNF V}
    (q : GeneralSA F) (B : ℝ) : Prop :=
  (∃ C d, d ∈ (q.multiplier C).support ∧ B ≤ |(q.multiplier C).coeff d|) ∨
  (∃ i d, d ∈ (q.booleanMultiplier i).support ∧ B ≤ |(q.booleanMultiplier i).coeff d|) ∨
  (∃ t, q.conical.coefficient t ≠ 0 ∧ B ≤ (q.conical.coefficient t : ℝ))

end UnaryParityLifting.Exact.Supplement


