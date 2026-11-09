-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_Model
-- name    : StabilityDichotomies_Solvability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:51.825044+00:00
-- url     : https://prove2.me/theorems/063dbff1-9a12-4928-8cbd-4f0c75cc3511
-- title:
--   Finite Boolean languages, multiset CSP instances, restrictions and solutions
-- statement:
--   A Boolean relation $R$ is a nonempty subset of $\{0,1\}^{r(R)}$ with $r(R)>0$. A language $\Gamma$ is a finite nonempty set of these relations. An instance $I=(V,C)$ has finite variables and a finite multiset of relation applications, with repeated variables allowed in each scope. Its solutions satisfy every occurrence:
--
--   $$\operatorname{Sol}(I)=\{x:V\to\{0,1\}:x(s_c)\in R_c\text{ for every }c\in C\}.$$
--
--   Deletion erases one copy and retains $V$. Variable restriction has carrier $U$ and retains all occurrences supported on $U$; constraint restriction retains $V$ and takes a submultiset. Relabelling applies a map to every scope. The constants are $r_\Gamma=\max_{R\in\Gamma}r(R)$ and $\kappa_\Gamma=\sum_{R\in\Gamma}2^{r(R)}|R|^2$, both positive for an admissible language.
--
--   This supplies a common instance and solution interface for every result in the mission.
--
--   **Formalization Note** Variables are arbitrary finite types, Boolean values are Bool, and coordinates are indexed from zero by Fin. The instance structure stores a multiset, so occurrence order and absent slots are not observable inputs. The generic type also exists for infinite carriers, but every theorem and the solver family use finite carriers.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), pp.2–3,7–8, Section 1.1 and Section 2.1; constants pp.8,14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib

noncomputable section

namespace StabilityDichotomies.Solvability

/-- Section 2.1, pp.7–8: a nonempty Boolean relation of positive arity. -/
structure Relation where
  arity : ℕ
  arity_pos : 0 < arity
  tuples : Finset (Fin arity → Bool)
  tuples_nonempty : tuples.Nonempty

/-- The language is a set, not an indexed family with possibly repeated relations. -/
structure Language where
  relations : Finset Relation
  relations_nonempty : relations.Nonempty

abbrev Language.Member (Γ : Language) := {R : Relation // R ∈ Γ.relations}

/-- Scopes may repeat variables. -/
structure Constraint (Γ : Language) (V : Type) where
  rel : Γ.Member
  scope : Fin rel.val.arity → V

/-- The carrier is fixed externally, so deletion retains even isolated variables. -/
structure Instance (Γ : Language) (V : Type) where
  constraints : Multiset (Constraint Γ V)

open scoped Classical

def maxArity (Γ : Language) : ℕ := Γ.relations.sup Relation.arity

def kappa (Γ : Language) : ℕ :=
  ∑ R ∈ Γ.relations, 2 ^ R.arity * R.tuples.card ^ 2

def Constraint.Satisfied {Γ : Language} {V : Type}
    (c : Constraint Γ V) (x : V → Bool) : Prop :=
  (fun i => x (c.scope i)) ∈ c.rel.val.tuples

def Solution {Γ : Language} {V : Type} (I : Instance Γ V) (x : V → Bool) : Prop :=
  ∀ c ∈ I.constraints, c.Satisfied x

def Satisfiable {Γ : Language} {V : Type} (I : Instance Γ V) : Prop :=
  ∃ x, Solution I x

/-- Remove one copy, never all equal copies. -/
def Instance.delete {Γ : Language} {V : Type}
    (I : Instance Γ V) (c : Constraint Γ V) : Instance Γ V :=
  ⟨I.constraints.erase c⟩

/-- Constraint restriction retains the carrier V. Used only when E ≤ I.constraints. -/
def Instance.restrictConstraints {Γ : Language} {V : Type}
    (I : Instance Γ V) (E : Multiset (Constraint Γ V))
    (_hE : E ≤ I.constraints) : Instance Γ V := ⟨E⟩

/-- Induced restriction has carrier U and retains every occurrence supported in U. -/
def Instance.induce {Γ : Language} {V : Type}
    (I : Instance Γ V) (U : Finset V) : Instance Γ U :=
  ⟨I.constraints.bind fun c =>
    if h : ∀ i, c.scope i ∈ U then
      {⟨c.rel, fun i => ⟨c.scope i, h i⟩⟩}
    else 0⟩

/-- Relabelling an instance uses the same map on every scope occurrence. -/
def Instance.map {Γ : Language} {V W : Type}
    (I : Instance Γ V) (f : V → W) : Instance Γ W :=
  ⟨I.constraints.map fun c => ⟨c.rel, f ∘ c.scope⟩⟩

end StabilityDichotomies.Solvability


