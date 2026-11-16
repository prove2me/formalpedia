-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_Supplement_EqualityFreePP
-- name    : StabilityDichotomies_Solvability_Supplement_EqualityFreePP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:35:09.560793+00:00
-- url     : https://prove2.me/theorems/60770d6f-aa80-4419-95f9-ecff72aa3e45
-- title:
--   Equality-free primitive-positive formulas and their bounded definitions
-- statement:
--   Let Γ and Λ be finite Boolean constraint languages. An equality-free primitive-positive formula F on k displayed free variables consists of t ≥ 0 existential variables and a finite list of Γ-relation applications. Arguments refer only to those free or existential variables, with arbitrary repetitions. Its meaning on a free assignment x is
--
--   $$F(x)\quad\Longleftrightarrow\quad \exists z\in\{0,1\}^{t},\ \bigwedge_{\alpha\in F}\alpha(x,z).$$
--
--   The bounded-definition property says that every relation R of Λ is exactly the existential projection of such a formula with at most a atomic occurrences and at most b existential variables. Empty conjunctions and zero existential variables are allowed. Scope substitution maps each atomic occurrence to a Γ-constraint without deduplication, on any target variable carrier.
--
--   This is the logical interface for Lemma 4.10. It contains only syntax, substitution and exact semantics; approximation and sensitivity are separate assertions. **Formalization Note** Free and existential variables use the disjoint sum of their finite index types; occurrences use a list before conversion to the base multiset model.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), canonical source.pdf, SHA-256 9eeb0875db685945a8b4c78bc4d30bfdbf3289a943d06f464836530d0eb22467. p.10, Definition 2.10 (equality-free case); p.22, Lemma 4.10(i).

import Definitions.Def_StabilityDichotomies_Solvability_Model

noncomputable section
open scoped Classical

namespace StabilityDichotomies.Solvability.Supplement

/-- Definition 2.10, p.10, restricted to equality-free formulas as in Lemma 4.10.
A list records atomic occurrences separately. There are no equality atoms or constants;
all argument positions refer to displayed free or existential variables. -/
structure EqualityFreePPFormula (Γ : Language) (k : ℕ) where
  existentialCount : ℕ
  atoms : List (Constraint Γ (Fin k ⊕ Fin existentialCount))

/-- Existential projection of the conjunction, including empty conjunctions and no witnesses. -/
def EqualityFreePPFormula.Holds {Γ : Language} {k : ℕ}
    (F : EqualityFreePPFormula Γ k) (x : Fin k → Bool) : Prop :=
  ∃ z : Fin F.existentialCount → Bool,
    ∀ c ∈ F.atoms, c.Satisfied (Sum.elim x z)

/-- Substitute scopes without collapsing repeated atoms or repeated variables. -/
def EqualityFreePPFormula.instantiate {Γ : Language} {k : ℕ} {V : Type}
    (F : EqualityFreePPFormula Γ k) (free : Fin k → V)
    (witness : Fin F.existentialCount → V) : Instance Γ V :=
  (⟨(F.atoms : Multiset _)⟩ : Instance Γ (Fin k ⊕ Fin F.existentialCount)).map
    (Sum.elim free witness)

/-- Lemma 4.10(i): syntax-size bounds and exact semantic equality, with no algorithmic claim. -/
def HasBoundedEqualityFreePPDefinitions (Λ Γ : Language) (a b : ℕ) : Prop :=
  ∀ R ∈ Λ.relations, ∃ F : EqualityFreePPFormula Γ R.arity,
    F.atoms.length ≤ a ∧ F.existentialCount ≤ b ∧
      ∀ x : Fin R.arity → Bool, x ∈ R.tuples ↔ F.Holds x

end StabilityDichotomies.Solvability.Supplement


