-- Prove2me | Definitions.Def_ArrighiStarFree_HalfLevel_Reductions
-- name    : ArrighiStarFree_HalfLevel_Reductions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:06:39.837781+00:00
-- url     : https://prove2.me/theorems/f457026a-4ef3-4a54-9ec3-c69cab7b0e8e
-- title:
--   Promise-preserving weak and logspace hardness and completeness
-- statement:
--   Let $A$ be an ordinary binary language and $P=(D,Y)$ a promise problem. A many-one reduction of a specified resource class is a total string map $f$ of that class satisfying
--   $$\forall x,\quad f(x)\in D\quad\text{and}\quad (Y(f(x))\Longleftrightarrow x\in A).$$
--   Thus both YES and NO inputs map to legal target instances. Hardness for L or NL quantifies over every language in that class, using the concrete machine definitions of class membership.
--
--   The predicates LHard and NLHard record two hardness assertions: uniform AC⁰ many-one hardness, as in the introduction and weak-reduction footnote, and deterministic logspace many-one hardness, as in the default convention of §2. Completeness is the corresponding membership assertion together with both hardness assertions.
--
--   These definitions impose resource bounds on the maps themselves and are independent of the paper's automata. There are no closure axioms or assumed reachability reductions.
-- source:
--   Arrighi et al. (2021), supplied source.pdf (arXiv:2110.01279v1), Introduction and §2–3, printed pp. 23:2–23:6, PDF pp. 2–6

import Definitions.Def_ArrighiStarFree_HalfLevel_AlternatingMachine

namespace ArrighiStarFree.HalfLevel

/-- Both YES and NO source strings are sent to legal target instances. -/
def Reduces (computable : (List Bool → List Bool) → Prop)
    (A : Set (List Bool)) (P : PromiseProblem) : Prop :=
  ∃ f, computable f ∧ ∀ x, f x ∈ P.domain ∧ (P.answer (f x) ↔ x ∈ A)

def HardFor (C : PromiseProblem → Prop)
    (computable : (List Bool → List Bool) → Prop) (P : PromiseProblem) : Prop :=
  ∀ A : Set (List Bool), C (totalProblem A) → Reduces computable A P

/-- Weak hardness from the introduction, together with ordinary logspace hardness
under the standing convention in §2. Neither is a hypothesis of the other. -/
def NLHard (P : PromiseProblem) : Prop :=
  HardFor InNL UniformAC0Computable P ∧ HardFor InNL LogspaceComputable P

def LHard (P : PromiseProblem) : Prop :=
  HardFor InL UniformAC0Computable P ∧ HardFor InL LogspaceComputable P

def NLComplete (P : PromiseProblem) : Prop := InNL P ∧ NLHard P

def LComplete (P : PromiseProblem) : Prop := InL P ∧ LHard P

end ArrighiStarFree.HalfLevel


