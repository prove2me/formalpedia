-- Prove2me | Definitions.Def_HypercliqueCircuits_Circuits_Supplement_DegreeCSP
-- name    : HypercliqueCircuits_Circuits_Supplement_DegreeCSP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:11:11.19097+00:00
-- url     : https://prove2.me/theorems/e18095d2-a1e5-4ec9-9629-3575ee694495
-- title:
--   Sparse degree-bounded Boolean polynomials and Max-Degree-kCSP instances
-- statement:
--   A constraint on $n$ Boolean variables is represented by a sparse integer polynomial
--
--   $$p(x)=\sum_{(S,c)\in p}c\prod_{i\in S}x_i.$$
--
--   A valid degree-$k$ constraint has distinct squarefree monomials, each containing at most $k$ variables, nonzero integer coefficients, and takes only the values 0 and 1 on every Boolean assignment. Variable lists in a monomial are strictly increasing; the order of distinct monomials is arbitrary. This is precisely the unique multilinear polynomial representation of a Boolean function, up to term order. Boolean multilinear coefficients are integers by Möbius inversion. There is no bound of $k$ on the total number of variables used across different monomials.
--
--   An instance is an indexed family $F$ of $m$ such polynomials. Repeated constraints and $m=0$ are permitted. Its score is
--
--   $$\operatorname{satisfiedCount}(F,x)=\#\{i<m:F_i(x)=1\}.$$
--
--   The input starts with $n,m$, then each constraint's term count and, for each term, the published signed encoding of its coefficient, its degree, and its increasing variable indices. Only finite polynomial data is input; no truth table, optimal assignment, or reduction certificate is supplied. This reusable polynomial interface supplies the full degree-bounded CSP problem rather than only clauses or bounded-arity constraints.
-- source:
--   Josh Alman, Baitian Li, Neha Pant, Kevin Pratt, Ryan Williams, Finding Hypercliques Faster Than Brute Force, STOC 2027 submission #1224 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1224.pdf, pp.2,26 (PDF 3,27), definition of degree-k constraint and Max-Degree-kCSP preceding Theorem 4

import Definitions.Def_HypercliqueCircuits_Circuits_Supplement_Encoding

set_option autoImplicit false

namespace HypercliqueCircuits.Circuits.Supplement

/-- A sparse integer polynomial in the squarefree {0,1} monomial basis.
Each term records a variable list and its signed coefficient. -/
abbrev ConstraintPolynomial (n : ℕ) := List (List (Fin n) × ℤ)

def constraintValue {n : ℕ} (p : ConstraintPolynomial n) (x : Fin n → Bool) : ℤ :=
  (p.map (fun term => term.2 *
    (term.1.map (fun i => (bit (x i) : ℤ))).prod)).sum

/-- Exactly the degree-at-most-k Boolean constraints of printed pp.2,26.
Strictly increasing variable lists are squarefree; distinct monomials and
nonzero coefficients make the representation unique up to term order.
No bound on the number of variables on which a constraint depends. -/
def IsDegreeConstraint {n : ℕ} (k : ℕ) (p : ConstraintPolynomial n) : Prop :=
  (∀ term ∈ p, term.1.Pairwise (fun i j => i.val < j.val) ∧
    term.1.length ≤ k ∧ term.2 ≠ 0) ∧
  (p.map Prod.fst).Nodup ∧
  ∀ x : Fin n → Bool, constraintValue p x = 0 ∨ constraintValue p x = 1

/-- Constraints are indexed, so repetitions and m = 0 are both allowed. -/
abbrev CSPInstance (n m : ℕ) := Fin m → ConstraintPolynomial n

def ValidCSP {n m : ℕ} (k : ℕ) (F : CSPInstance n m) : Prop :=
  ∀ i : Fin m, IsDegreeConstraint k (F i)

def satisfiedCount {n m : ℕ} (F : CSPInstance n m) (x : Fin n → Bool) : ℕ :=
  ((List.finRange m).filter (fun i => constraintValue (F i) x = 1)).length

/-- A length-prefixed sparse polynomial: number of terms, then for every
term its signedWord coefficient, degree, and increasing variable indices. -/
def constraintWords {n : ℕ} (p : ConstraintPolynomial n) : List ℕ :=
  p.length :: p.flatMap (fun term =>
    signedWord term.2 :: term.1.length :: term.1.map Fin.val)

def cspInput {n m : ℕ} (F : CSPInstance n m) : List (Cell Empty) :=
  words ([n, m] ++ (List.finRange m).flatMap (fun i => constraintWords (F i)))

end HypercliqueCircuits.Circuits.Supplement


