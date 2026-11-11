-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_Ordering
-- name    : SatisfiableOrderingCSP_Optimal_Ordering
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:44:15.331607+00:00
-- url     : https://prove2.me/theorems/33a60ce7-0ec1-430c-8a5d-b203a07d5843
-- title:
--   Ordering predicates, weighted instances, and canonical relaxations
-- statement:
--   An ordering predicate consists of an arity at least two and a nonempty proper set of satisfying permutations. A language is a nonempty finite set of such predicates. An instance has finitely many variables, a nonempty indexed list of constraints with injective scopes, and strictly positive real weights summing to one. Its score is the weighted sum of satisfied constraints and its value is the maximum score over all permutations. Repeated constraints and isolated variables are allowed. NFirst means that some listed argument precedes the distinguished argument; NLast reverses this comparison. The left and right canonical relaxations conjoin every implied NFirst or NLast relation, respectively; an empty conjunction is true. Canonical feasibility means that two orders satisfy the respective relaxations. Local types retain the predicate and the two patterns in argument order.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; Definition 1.1; Definition 4.1; pp. 1, 17 (PDF 4, 20)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Order (n : ℕ) := Equiv.Perm (Fin n)

/-- A nonconstant ordering relation, represented by its satisfying full rank patterns. -/
structure Predicate where
  arity : ℕ
  arity_ge : 2 ≤ arity
  sat : Finset (Order arity)
  sat_nonempty : sat.Nonempty
  sat_proper : sat ≠ Finset.univ

/-- A nonempty finite ordering language; predicates may have different arities. -/
structure Language where
  predicates : Finset Predicate
  nonempty : predicates.Nonempty

def HasPattern {k : ℕ} {α : Type} [LT α] (x : Fin k → α) (τ : Order k) : Prop :=
  ∀ i j, x i < x j ↔ τ i < τ j

def Predicate.Accepts {α : Type} [LT α] (φ : Predicate) (x : Fin φ.arity → α) : Prop :=
  ∃ τ ∈ φ.sat, HasPattern x τ

structure Constraint (n : ℕ) where
  predicate : Predicate
  scope : Fin predicate.arity ↪ Fin n

/-- Indexed occurrences retain repetitions, isolated variables, and positive real weights. -/
structure Instance where
  n : ℕ
  m : ℕ
  m_pos : 0 < m
  constraint : Fin m → Constraint n
  weight : Fin m → ℝ
  weight_pos : ∀ c, 0 < weight c
  weight_sum : ∑ c, weight c = 1

def Instance.Over (I : Instance) (Lg : Language) : Prop :=
  ∀ c, (I.constraint c).predicate ∈ Lg.predicates

def Instance.score (I : Instance) (π : Order I.n) : ℝ :=
  ∑ c, I.weight c * if (I.constraint c).predicate.Accepts
    (fun j => π ((I.constraint c).scope j)) then 1 else 0

/-- The supremum is a maximum: the permutation type is finite and contains the identity. -/
def Instance.value (I : Instance) : ℝ := sSup (Set.range I.score)

def Instance.Unweighted (I : Instance) : Prop := ∀ c, I.weight c = 1 / (I.m : ℝ)

def NFirst {k : ℕ} (π : Order k) (x : Fin k) (S : Finset (Fin k)) : Prop :=
  ∃ y ∈ S, π y < π x

def NLast {k : ℕ} (π : Order k) (x : Fin k) (S : Finset (Fin k)) : Prop :=
  ∃ y ∈ S, π x < π y

def LeftRelax (φ : Predicate) (π : Order φ.arity) : Prop :=
  ∀ x S, S.Nonempty → x ∉ S → (∀ τ ∈ φ.sat, NFirst τ x S) → NFirst π x S

def RightRelax (φ : Predicate) (π : Order φ.arity) : Prop :=
  ∀ x S, S.Nonempty → x ∉ S → (∀ τ ∈ φ.sat, NLast τ x S) → NLast π x S

def Instance.RelaxedOrders (I : Instance) (L R : Order I.n) : Prop :=
  ∀ c, (∃ τ, HasPattern (fun j => L ((I.constraint c).scope j)) τ ∧
      LeftRelax (I.constraint c).predicate τ) ∧
    (∃ τ, HasPattern (fun j => R ((I.constraint c).scope j)) τ ∧
      RightRelax (I.constraint c).predicate τ)

def Instance.CanonicallyFeasible (I : Instance) : Prop := ∃ L R, I.RelaxedOrders L R

structure LocalType where
  predicate : Predicate
  left : Order predicate.arity
  right : Order predicate.arity

def LocalType.Eligible (d : LocalType) (Lg : Language) : Prop :=
  d.predicate ∈ Lg.predicates ∧ LeftRelax d.predicate d.left ∧ RightRelax d.predicate d.right

end
end SatisfiableOrderingCSP.Optimal


