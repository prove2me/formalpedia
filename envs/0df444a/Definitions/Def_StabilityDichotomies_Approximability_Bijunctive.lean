-- Prove2me | Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
-- name    : StabilityDichotomies_Approximability_Bijunctive
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:41:47.806794+00:00
-- url     : https://prove2.me/theorems/f3a93550-1a48-4dcb-8aca-7f725919aace
-- title:
--   Deterministic core of the bijunctive priority-and-shift algorithm
-- statement:
--   A fixed positive-bounded 2-CNF representation is given for every relation in a Boolean language. The definitions substitute scopes, omit tautologies, form the implication adjacency relation, measure shortest directed path length, test literal feasibility in a second subinstance, and compute scores as maxima over feasible roots. For prescribed occurrence priorities, cutoff and literal shifts, the output map forms the two nested threshold subinstances and compares the positive and negative literal scores as in Definition 4.8. Unit clauses remain duplicated pairs, and adjacency forgets arc multiplicity because only shortest-path distances are used. This module defines the deterministic core only: it does not yet specify the probability distribution of the priorities, cutoff or shifts, assert representation existence, or model runtime.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Definitions 4.7–4.8, pp. 19–20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Approximability_Thinning

noncomputable section
open scoped Classical BigOperators
namespace StabilityDichotomies.Bijunctive
open StabilityDichotomies.Solvability

/-- A Boolean literal pairs a variable with its satisfying truth value. -/
abbrev Literal (V : Type) := V × Bool

def literalNeg {V : Type} (a : Literal V) : Literal V := (a.1, !a.2)
def literalValue {V : Type} (x : V → Bool) (a : Literal V) : Bool := x a.1 == a.2

/-- A two-CNF clause; equal literals represent a unit clause. -/
abbrev Clause (V : Type) := Literal V × Literal V

def clauseSatisfied {V : Type} (x : V → Bool) (q : Clause V) : Prop :=
  literalValue x q.1 = true ∨ literalValue x q.2 = true

/-- Fixed source representations, including an explicit positive uniform clause bound. -/
structure TwoCNFRepresentation (Γ : Language) where
  clauses : ∀ R : Γ.Member, List (Clause (Fin R.val.arity))
  correct : ∀ (R : Γ.Member) (x : Fin R.val.arity → Bool),
    x ∈ R.val.tuples ↔ ∀ q ∈ clauses R, clauseSatisfied x q
  clauseBound : ℕ
  clauseBound_pos : 0 < clauseBound
  clauseBound_spec : ∀ R : Γ.Member, (clauses R).length ≤ clauseBound

/-- Substitute the scope variables into a relation's fixed defining clause. -/
def substituteClause {Γ : Language} {V : Type} (c : Constraint Γ V)
    (q : Clause (Fin c.rel.val.arity)) : Clause V :=
  ((c.scope q.1.1, q.1.2), (c.scope q.2.1, q.2.2))

/-- Adjacency of Definition 4.7. Tautologies after substitution are discarded; unit clauses retain
both identical implications. Arc multiplicity does not affect reachability or shortest-path length. -/
def implicationArc {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (I : Instance Γ V) (a b : Literal V) : Prop :=
  ∃ c ∈ I.constraints, ∃ q ∈ rep.clauses c.rel,
    let z := substituteClause c q
    z.1 ≠ literalNeg z.2 ∧
      ((a = literalNeg z.1 ∧ b = z.2) ∨ (a = literalNeg z.2 ∧ b = z.1))

/-- Directed walks counted by their number of unit-length arcs. -/
inductive WalkLength {α : Type} (arc : α → α → Prop) : ℕ → α → α → Prop
  | zero (a : α) : WalkLength arc 0 a a
  | step {n : ℕ} {a b c : α} : arc a b → WalkLength arc n b c → WalkLength arc (n+1) a c

/-- A finite shortest-path distance, or `none` for an unreachable literal. -/
def implicationDistance {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (I : Instance Γ V) (a b : Literal V) : Option ℕ :=
  if h : ∃ n : ℕ, WalkLength (implicationArc rep I) n a b then some (Nat.find h) else none

/-- A literal is feasible if some solution makes it true. -/
def feasibleLiteral {Γ : Language} {V : Type} (I : Instance Γ V) (a : Literal V) : Prop :=
  ∃ x : V → Bool, Solution I x ∧ literalValue x a = true

/-- The paper's maximum over feasible roots; unreachable roots contribute bottom. -/
def literalScore {Γ : Language} {V : Type} [Fintype V] (rep : TwoCNFRepresentation Γ)
    (graphInstance feasibleInstance : Instance Γ V) (shifts : Literal V → ℝ) (target : Literal V) : WithBot ℝ :=
  Finset.univ.sup fun root : Literal V =>
    if feasibleLiteral feasibleInstance root then
      match implicationDistance rep graphInstance root target with
      | some n => ((shifts root - n : ℝ) : WithBot ℝ)
      | none => ⊥
    else ⊥

/-- The deterministic map used by Definition 4.8 for given priorities, cutoff and shifts. -/
def bijunctiveOutput {Γ : Language} {V : Type} [Fintype V] (rep : TwoCNFRepresentation Γ)
    (I : Instance Γ V) (ε : ℝ) (priority : Fin I.constraints.card → ℝ)
    (cutoff : ℝ) (shifts : Literal V → ℝ) : V → Bool :=
  let first := thinnedInstance I (fun i => decide (priority i ≤ 1 - ε / 2))
  let second := thinnedInstance I (fun i => decide (priority i ≤ cutoff))
  fun v => decide (literalScore rep first second shifts (v, true) >
                   literalScore rep first second shifts (v, false))

/-- The exponential rate specified by Definition 4.8. -/
def bijunctiveRate {Γ : Language} (rep : TwoCNFRepresentation Γ) (ε : ℝ) : ℝ :=
  ε / (2 * rep.clauseBound)

end StabilityDichotomies.Bijunctive


