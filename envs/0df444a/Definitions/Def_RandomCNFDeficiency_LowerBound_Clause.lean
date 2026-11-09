-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_Clause
-- name    : RandomCNFDeficiency_LowerBound_Clause
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:44.537119+00:00
-- url     : https://prove2.me/theorems/18b41659-30c3-405e-bad3-87024f409c5f
-- title:
--   Signed clauses, neighborhoods and partial satisfaction
-- statement:
--   A signed clause on the variables $[n]$ assigns each variable either no occurrence, a positive literal, or a negative literal. An assignment satisfies it when it gives one occurring variable the prescribed sign. A finite CNF is a finite set of clauses, and it is satisfiable when one assignment satisfies every clause. Write $N(A)$ for the union of the variable supports in $A$.
--
--   $$N(A)=\bigcup_{C\in A}\operatorname{supp}(C).$$
--
--   A partial assignment satisfies a clause only if it assigns a literal of that clause a satisfying value. These definitions allow heterogeneous clause widths, including the empty clause, as the deterministic results require. The exact-width random clauses and assignment carrier use the published FixedClauseThreshold model. Variable indices are shifted from $[n]$ to $\{0,\ldots,n-1\}$ without changing any instance.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 2 and Lemma 3.5, printed p. 5, PDF p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf; printed p. 10, PDF p. 12

import Mathlib
import Definitions.Def_FixedClauseThreshold
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound

/-- A heterogeneous-width signed clause; the raw carrier of the published ProperClause. -/
abbrev Clause (n : ℕ) := Fin n → Option Bool

abbrev Assignment (n : ℕ) := OAI.FixedClauseThreshold.Assignment n

abbrev CNF (n : ℕ) := Finset (Clause n)

def clauseSupport {n : ℕ} (C : Clause n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (C i).isSome

def clauseWidth {n : ℕ} (C : Clause n) : ℕ := (clauseSupport C).card

def SatisfiesClause {n : ℕ} (a : Assignment n) (C : Clause n) : Prop :=
  ∃ i, C i = some (a i)

def Satisfiable {n : ℕ} (F : CNF n) : Prop :=
  ∃ a : Assignment n, ∀ C ∈ F, SatisfiesClause a C

noncomputable def neighborhood {n : ℕ} (F : CNF n) : Finset (Fin n) :=
  F.biUnion clauseSupport

/-- A partial assignment satisfies a literal by actually assigning its variable. -/
def PartialSatisfies {n : ℕ} (ρ : Fin n → Option Bool) (C : Clause n) : Prop :=
  ∃ i b, ρ i = some b ∧ C i = some b

end RandomCNFDeficiency.LowerBound


