-- Prove2me | Definitions.Def_CNFLearning873_Valiant_CNF
-- name    : CNFLearning873_Valiant_CNF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:02:46.308198+00:00
-- url     : https://prove2.me/theorems/a2a4e8b4-942c-4a2d-a315-bb6466b5742f
-- title:
--   Bounded-degree signed CNF model
-- statement:
--   Let $V=\{0,\ldots,n-1\}$ and let an assignment be a map $V\to\{0,1\}$. The published signed-clause model records a satisfying literal sign or absence at each variable. Negating each present sign recovers the source's forbidden assignment. A formula $F$ is a finite set of these clauses, and $\Omega(F)$ is its actual set of satisfying assignments.
--
--   $$\operatorname{KD}(F,k,d)\iff (\forall c\in F,\ |\operatorname{vbl}(c)|=k)\ \land\ (\forall v,\ |\{c\in F:v\in\operatorname{vbl}(c)\}|\le d).$$
--
--   Variable-width bounds, candidate clauses, subclause containment, restriction, and violation use this same representation. Empty formulas and isolated variables are included. This is the common model for every source result in the mission.
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Definition 1.2, pp.2–3; §3, p.11 (PDF pp.2–3,11)

import Definitions.Def_RandomCNFDeficiency_LowerBound_Clause

namespace CNFLearning873.Valiant

open scoped BigOperators

abbrev Clause := RandomCNFDeficiency.LowerBound.Clause
abbrev Assignment := RandomCNFDeficiency.LowerBound.Assignment
abbrev CNF := RandomCNFDeficiency.LowerBound.CNF
abbrev support := @RandomCNFDeficiency.LowerBound.clauseSupport
abbrev width := @RandomCNFDeficiency.LowerBound.clauseWidth
abbrev Sat := @RandomCNFDeficiency.LowerBound.SatisfiesClause

/-- Literal signs are satisfying values; the source's forbidden value is their negation.
Feng--Yu--Zhang, STOC 2027 submission #873 (October 2026), pp.2,11 (PDF pp.2,11). -/
def Violates {n : ℕ} (c : Clause n) (x : Assignment n) : Prop := ¬ Sat x c

noncomputable def solutions {n : ℕ} (F : CNF n) : Finset (Assignment n) := by
  classical
  exact Finset.univ.filter fun x => ∀ c ∈ F, Sat x c

def DegreeBound {n : ℕ} (F : CNF n) (d : ℕ) : Prop :=
  ∀ v, (F.filter fun c => v ∈ support c).card ≤ d

def WidthBounds {n : ℕ} (F : CNF n) (k₁ k₂ : ℕ) : Prop :=
  ∀ c ∈ F, k₁ ≤ width c ∧ width c ≤ k₂

def KD {n : ℕ} (F : CNF n) (k d : ℕ) : Prop :=
  (∀ c ∈ F, width c = k) ∧ DegreeBound F d

noncomputable def candidates (n k : ℕ) : CNF n := by
  classical
  exact Finset.univ.filter fun c => width c = k

def Subclause {n : ℕ} (s c : Clause n) : Prop :=
  ∀ v b, s v = some b → c v = some b

def restrict {n : ℕ} (c : Clause n) (U : Finset (Fin n)) : Clause n :=
  fun v => if v ∈ U then c v else none

end CNFLearning873.Valiant


