-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_FiniteDuality
-- name    : StabilityDichotomies_Solvability_FiniteDuality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:25.934604+00:00
-- url     : https://prove2.me/theorems/09b5471e-c33f-4657-9328-ab67fc340c90
-- title:
--   Semantic finite duality and strict essential Boolean CNF classes
-- statement:
--   Finite duality means that unsatisfiability is always witnessed on a bounded number of variables, with one bound for the language:
--
--   $$\exists d_\Gamma\in\mathbb N\ \forall I\in\operatorname{CSP}(\Gamma),\quad \operatorname{Sol}(I)=\varnothing\ \Longrightarrow\ \exists U\subseteq V(I),\ |U|\le d_\Gamma,\ \operatorname{Sol}(I[U])=\varnothing.$$
--
--   A CNF defines a relation when its satisfying tuples are exactly the relation. Strict essential positivity permits only unit clauses and clauses of positive literals; strict essential negativity permits only unit clauses and clauses of negative literals. Clauses use only the relation's own coordinates. There are no existential coordinates or additional equality atoms. A language is $b$-valid if every relation contains its constant $b$ tuple; it has a strict essential class if every relation has that class.
--
--   These independent semantic and syntactic definitions make the criterion of Proposition 2.6 substantive. Literal signs are Boolean desired values. Finite lists represent clauses and CNFs; the empty CNF is true and the empty clause is false.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), pp.8–9, Definitions 2.2,2.4,2.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_Model

noncomputable section

namespace StabilityDichotomies.Solvability

open scoped Classical

/-- Definition 2.4, p.9; the bound precedes all finite carriers and all instances. -/
def FiniteDuality (Γ : Language) : Prop :=
  ∃ d : ℕ, ∀ (V : Type) [Fintype V] (I : Instance Γ V),
    ¬ Satisfiable I → ∃ U : Finset V, U.card ≤ d ∧ ¬ Satisfiable (I.induce U)

abbrev Literal (r : ℕ) := Fin r × Bool
abbrev Clause (r : ℕ) := List (Literal r)
abbrev CNF (r : ℕ) := List (Clause r)

def ClauseHolds {r : ℕ} (c : Clause r) (x : Fin r → Bool) : Prop :=
  ∃ l ∈ c, x l.1 = l.2

def CNFHolds {r : ℕ} (f : CNF r) (x : Fin r → Bool) : Prop :=
  ∀ c ∈ f, ClauseHolds c x

/-- Clauses use only the relation's own arguments, with no existential variables. -/
def StrictEssential (positive : Bool) (R : Relation) : Prop :=
  ∃ f : CNF R.arity,
    (∀ c ∈ f, c.length = 1 ∨ ∀ l ∈ c, l.2 = positive) ∧
    ∀ x, x ∈ R.tuples ↔ CNFHolds f x

def Valid (Γ : Language) (b : Bool) : Prop :=
  ∀ R ∈ Γ.relations, (fun _ : Fin R.arity => b) ∈ R.tuples

def StrictEssentialLanguage (Γ : Language) (positive : Bool) : Prop :=
  ∀ R ∈ Γ.relations, StrictEssential positive R

end StabilityDichotomies.Solvability


