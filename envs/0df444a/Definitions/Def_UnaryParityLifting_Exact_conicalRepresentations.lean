-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_conicalRepresentations
-- name    : UnaryParityLifting_Exact_conicalRepresentations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:53.166503+00:00
-- url     : https://prove2.me/theorems/832ea117-902d-4f80-8e7e-70641ebddd2a
-- title:
--   Conical representations and exact real SA certificates
-- statement:
--   For a finite set $V$ of Boolean variables, a term selects some coordinates and one required bit for each selected coordinate. Its polynomial is
--   $$t(z)=\prod_{i:t_i=1}z_i\prod_{j:t_j=0}(1-z_j).$$
--   Unselected coordinates contribute one. Its degree counts selected coordinates, so the empty term is one and has degree zero. A conical representation assigns a nonnegative real coefficient $\lambda_t$ to each distinct term. It defines both a real multilinear polynomial and its Boolean-cube function, with mass $\sum_t\lambda_t$. Degree at most $R$ constrains every term of nonzero coefficient before cancellation.
--
--   A real certificate for $F$ additionally assigns a nonnegative real constant $a_C$ to each original clause. Exactness means the formal polynomial identity
--   $$\sum_{C\in F}a_C\overline C=1+\sum_t\lambda_t t.$$
--   No Boolean-axiom multipliers are present. Its degree also bounds the width of every clause with nonzero axiom coefficient. Its mass is $\sum_C a_C+\sum_t\lambda_t$, and its axiom support counts nonzero $a_C$, independently of the conical support.
--
--   Multilinearity means every exponent in every supported monomial is at most one. For a cube function, a multilinear degree bound asserts existence of a multilinear polynomial of that degree representing it. These definitions preserve the source's distinction between conical degree, polynomial degree, and coefficient mass, including zero polynomials and empty terms.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.6–7, Definition 2.2, equations (2.1)–(2.4); pp.14–15, equations (4.4)–(4.6)

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_certificateSyntax

namespace UnaryParityLifting.Exact

open scoped BigOperators

/-- A consistent conjunction of literals, with none meaning absent. Empty term is all none. -/
abbrev Term (V : Type*) := V → Option Bool

noncomputable def termDegree {V : Type*} [Fintype V] [DecidableEq V] (t : Term V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => (t v).isSome)).card

noncomputable def termPolynomial {V : Type*} [Fintype V] [DecidableEq V] (t : Term V) : MvPolynomial V ℝ :=
  ∏ v, match t v with
    | none => 1
    | some true => MvPolynomial.X v
    | some false => 1 - MvPolynomial.X v

noncomputable def termValue {V : Type*} [Fintype V] [DecidableEq V] (t : Term V) (x : V → Bool) : ℝ :=
  MvPolynomial.eval (fun v => realBit (x v)) (termPolynomial t)

/-- One nonnegative coefficient per distinct term; coefficients have already been collected. -/
structure ConicalRepresentation (V : Type*) where
  coefficient : Term V → NNReal

noncomputable def ConicalRepresentation.polynomial {V : Type*} [Fintype V] [DecidableEq V]
    (q : ConicalRepresentation V) : MvPolynomial V ℝ :=
  ∑ t : Term V, MvPolynomial.C (q.coefficient t : ℝ) * termPolynomial t

noncomputable def ConicalRepresentation.value {V : Type*} [Fintype V] [DecidableEq V]
    (q : ConicalRepresentation V) (x : V → Bool) : ℝ :=
  ∑ t : Term V, (q.coefficient t : ℝ) * termValue t x

noncomputable def ConicalRepresentation.mass {V : Type*} [Fintype V] [DecidableEq V]
    (q : ConicalRepresentation V) : ℝ := ∑ t : Term V, (q.coefficient t : ℝ)

noncomputable def ConicalRepresentation.DegreeLE {V : Type*} [Fintype V] [DecidableEq V]
    (q : ConicalRepresentation V) (R : ℕ) : Prop :=
  ∀ t, q.coefficient t ≠ 0 → termDegree t ≤ R

/-- Canonical multilinearity in the monomial basis, not merely equality on the cube. -/
def Multilinear {V : Type*} (p : MvPolynomial V ℝ) : Prop :=
  ∀ d ∈ p.support, ∀ v, d v ≤ 1

/-- Degree of the unique multilinear representative of a cube function. -/
noncomputable def MultilinearDegreeLE {V : Type*} (f : (V → Bool) → ℝ) (R : ℕ) : Prop :=
  ∃ p : MvPolynomial V ℝ, Multilinear p ∧ p.totalDegree ≤ R ∧
    ∀ x, MvPolynomial.eval (fun v => realBit (x v)) p = f x

/-- Real output coefficients are constants indexed by original axioms. -/
structure RealCertificate {V : Type*} (F : LiftSAParity.CNF V) where
  axiomCoefficient : {C // C ∈ F} → NNReal
  conical : ConicalRepresentation V

/-- Exact equality of real polynomials, without Boolean-axiom multipliers. -/
noncomputable def RealCertificate.IsExact {V : Type*} [Fintype V] [DecidableEq V]
    {F : LiftSAParity.CNF V} (q : RealCertificate F) : Prop :=
  (∑ C : {C // C ∈ F}, MvPolynomial.C (q.axiomCoefficient C : ℝ) * clausePolynomial C.val) =
    1 + q.conical.polynomial

/-- Termwise degree before cancellation, including the nonzero axiom summands. -/
noncomputable def RealCertificate.DegreeLE {V : Type*} [Fintype V] [DecidableEq V]
    {F : LiftSAParity.CNF V} (q : RealCertificate F) (R : ℕ) : Prop :=
  (∀ C, q.axiomCoefficient C ≠ 0 → C.val.card ≤ R) ∧ q.conical.DegreeLE R

noncomputable def RealCertificate.mass {V : Type*} [Fintype V] [DecidableEq V]
    {F : LiftSAParity.CNF V} (q : RealCertificate F) : ℝ :=
  (∑ C : {C // C ∈ F}, (q.axiomCoefficient C : ℝ)) + q.conical.mass

noncomputable def RealCertificate.axiomSupport {V : Type*}
    {F : LiftSAParity.CNF V} (q : RealCertificate F) : ℕ := by
  classical
  exact (Finset.univ.filter (fun C => q.axiomCoefficient C ≠ 0)).card

end UnaryParityLifting.Exact


