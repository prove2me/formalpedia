-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Formula
-- name    : ChvatalOneHard398_SAT_Formula
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:38.946676+00:00
-- url     : https://prove2.me/theorems/04ba51c8-2b6f-4c96-9196-943e1556e874
-- title:
--   Literals, SAT polytopes, and the exact-one to SAT construction
-- statement:
--   The published JohnsonApprox literal and clause types are reused: a literal is a variable or its complement, and a clause is a finite set of literals. Its separate partial-assignment and MAX-SAT definitions are unused. A formula records its variable count and a finite list of clauses. Well-formedness requires nonempty clauses and variable identifiers below that count. On a real vector $x$, a positive literal has value $x_i$ and a negative literal has value $1-x_i$.
--
--   $$P(F)=\{x\in[0,1]^N:\sum_{\ell\in T}\ell(x)\ge1\text{ for every }T\in F\},\qquad X(T)=\{x\in[0,1]^N:\sum_{\ell\in C}\ell(x)=1\text{ for every }C\in T\}.$$
--
--   Satisfiability is the existence of a Boolean assignment making a literal true in each clause. The target promise is exactly well-formedness, at most three literals per clause, and $P(F)'=P(F)_I$. The concrete exact-one conversion splits long rows with fresh chain variables, then introduces the at-least-one clause and pairwise complement clauses. Its ordering is by variable identifier and polarity. This is the construction in Lemma 18, without any assumed guarantees.
--
--   **Formalization Note** Variable identifiers are zero-based natural numbers with a separate range check. Raw malformed formulas remain available outside the promise. Empty families of clauses are allowed; an empty clause is excluded by well-formedness. Repeated clauses do not change the polytope, while literal multiplicity is removed by finite sets.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.17, §5, SAT polytope; pp.19–20, exact-one systems and proof of Lemma 18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Geometry
import Definitions.Def_JohnsonApprox_Shared_Problem

namespace ChvatalOneHard398.SAT
open scoped BigOperators

/-- Natural variable identifiers, checked against N by WellFormed; true means positive. -/
abbrev Literal := JohnsonApprox.Shared.Literal
abbrev Clause := JohnsonApprox.Shared.Clause

instance : Inhabited Literal := ⟨⟨0,false⟩⟩

structure Formula where
  N : ℕ
  clauses : List Clause

def negLit (l : Literal) : Literal := l.neg

def Formula.WellFormed (F : Formula) : Prop :=
  ∀ T ∈ F.clauses, T.Nonempty ∧ ∀ l ∈ T, l.var < F.N

noncomputable def literalValue {N : ℕ} (x : Fin N → ℝ) (l : Literal) : ℝ :=
  if h : l.var < N then if l.pos then x ⟨l.var, h⟩ else 1 - x ⟨l.var, h⟩ else 0

def literalTruth {N : ℕ} (a : Fin N → Bool) (l : Literal) : Bool :=
  if h : l.var < N then if l.pos then a ⟨l.var, h⟩ else !(a ⟨l.var, h⟩) else false

def Satisfies (F : Formula) (a : Fin F.N → Bool) : Prop :=
  ∀ T ∈ F.clauses, ∃ l ∈ T, literalTruth a l = true

def Satisfiable (F : Formula) : Prop := ∃ a, Satisfies F a

def assignments (F : Formula) := {a : Fin F.N → Bool // Satisfies F a}

noncomputable def satPolytope (F : Formula) : Set (Fin F.N → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ T ∈ F.clauses, 1 ≤ ∑ l ∈ T, literalValue x l}

noncomputable def exactOne (F : Formula) : Set (Fin F.N → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ T ∈ F.clauses, ∑ l ∈ T, literalValue x l = 1}

noncomputable def TargetPromise (F : Formula) : Prop :=
  F.WellFormed ∧ (∀ T ∈ F.clauses, T.card ≤ 3) ∧ rankOne (satPolytope F)

/-- Canonical ordering by variable, then polarity. -/
def orderedLiterals (T : Clause) : List Literal := ((T.image (fun l => 2 * l.var + if l.pos then 1 else 0)).sort (· ≤ ·)).map
    (fun k => (⟨k / 2, decide (k % 2 = 1)⟩ : Literal))

/-- Split a single large exact-one row, with the new identifiers beginning at N. -/
def splitRow (N : ℕ) (T : Clause) : ℕ × List Clause := Id.run do
  let ls := orderedLiterals T
  let k := ls.length
  if k ≤ 3 then return (N, [T])
  let mut rows : List Clause := [([ls[0]!, ls[1]!, ⟨N, true⟩] : List Literal).toFinset]
  for j in List.range (k - 4) do
    rows := rows ++ [([⟨N + j, false⟩, ls[j + 2]!, ⟨N + j + 1, true⟩] : List Literal).toFinset]
  rows := rows ++ [([⟨N + (k - 4), false⟩, ls[k - 2]!, ls[k - 1]!] : List Literal).toFinset]
  return (N + k - 3, rows)

def splitExact (T : Formula) : Formula :=
  let z := T.clauses.foldl (fun (s : ℕ × List Clause) row =>
    let r := splitRow s.1 row
    (r.1, s.2 ++ r.2)) (T.N, [])
  ⟨z.1, z.2⟩

/-- At-least-one, together with the pairwise at-most-one clauses. -/
def rowClauses (T : Clause) : List Clause :=
  let ls := orderedLiterals T
  T :: ((List.range ls.length).flatMap fun i =>
    ((List.range ls.length).filter (i < ·)).map fun j =>
      ([negLit ls[i]!, negLit ls[j]!] : List Literal).toFinset)

def exactToSAT (T : Formula) : Formula :=
  let U := splitExact T
  ⟨U.N, U.clauses.flatMap rowClauses⟩

def literalCount (T : Formula) : ℕ := (T.clauses.map Finset.card).sum

end ChvatalOneHard398.SAT


