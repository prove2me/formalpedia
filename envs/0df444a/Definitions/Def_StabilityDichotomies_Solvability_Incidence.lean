-- Prove2me | Definitions.Def_StabilityDichotomies_Solvability_Incidence
-- name    : StabilityDichotomies_Solvability_Incidence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:32.690199+00:00
-- url     : https://prove2.me/theorems/7e43dc04-88e7-4ec5-92d6-0eada37ac026
-- title:
--   Minimal unsatisfiability and the constraint-occurrence incidence graph
-- statement:
--   An instance is minimally unsatisfiable if it has no solution and every one-occurrence deletion has a solution:
--
--   $$\operatorname{Sol}(I)=\varnothing\quad\text{and}\quad \forall c\in C,\ \operatorname{Sol}(I-c)\ne\varnothing.$$
--
--   The incidence graph has disjoint variable and constraint-occurrence vertices, with an edge from an occurrence $c$ to $v$ exactly when $v$ appears in its scope. Repeated appearance in one scope gives one edge; equal constraints still have separate occurrence vertices.
--
--   The graph supplies paths, distances and diameter for the lower-bound milestones. Occurrence indices come from a chosen representative list of the multiset only inside this graph. They never enter an instance or a solver input. Changing the representative permutes occurrence vertices and preserves every graph assertion. Isolated variables remain graph vertices. Distances and diameter use Mathlib's extended natural values, with unreachable pairs at infinity.
-- source:
--   Chunyang Wang, Yuichi Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535 (October 2026), pp.11–12, Definitions 3.2 and 3.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Definitions.Def_StabilityDichotomies_Solvability_Model

noncomputable section

namespace StabilityDichotomies.Solvability

open scoped Classical

/-- Definition 3.2, p.11. -/
def MinimallyUnsatisfiable {Γ : Language} {V : Type} (I : Instance Γ V) : Prop :=
  ¬ Satisfiable I ∧ ∀ c ∈ I.constraints, Satisfiable (I.delete c)

/-- Occurrences are indexed only for graph vertices, never for solver input.
Multiset.toList chooses a representative; different choices give isomorphic graphs. -/
abbrev Occurrence {Γ : Language} {V : Type} (I : Instance Γ V) :=
  Fin I.constraints.toList.length

def occurrenceConstraint {Γ : Language} {V : Type}
    (I : Instance Γ V) (i : Occurrence I) : Constraint Γ V :=
  I.constraints.toList.get i

abbrev IncidenceVertex {Γ : Language} {V : Type} (I : Instance Γ V) :=
  V ⊕ Occurrence I

def IncAdjacent {Γ : Language} {V : Type} (I : Instance Γ V) :
    IncidenceVertex I → IncidenceVertex I → Prop
  | .inl v, .inr c => ∃ i, (occurrenceConstraint I c).scope i = v
  | .inr c, .inl v => ∃ i, (occurrenceConstraint I c).scope i = v
  | _, _ => False

/-- Definition 3.3, p.12. An edge records occurrence, ignoring within-scope repetition. -/
def incidenceGraph {Γ : Language} {V : Type} (I : Instance Γ V) :
    SimpleGraph (IncidenceVertex I) where
  Adj := IncAdjacent I
  symm := ⟨by intro u v; cases u <;> cases v <;> simp_all [IncAdjacent]⟩
  loopless := ⟨by intro u; cases u <;> simp [IncAdjacent]⟩

end StabilityDichotomies.Solvability


