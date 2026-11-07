-- Prove2me | Definitions.Def_ReadTwiceCount_UPStep
-- name    : ReadTwiceCount_UPStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:36.063683+00:00
-- url     : https://prove2.me/theorems/397428f4-e79f-464f-972e-12e93996bcbd
-- title:
--   Unit propagation steps and termination
-- statement:
--   A **unit clause** on a literal $l$ is a nonempty clause all of whose literals are $l$ (so $(x\vee x)$ is a unit clause on $x$). A **unit-propagation step** takes a formula $G$ with a unit clause on $l$ to the formula obtained from $G$ by pinning $l$ true. Propagation has **terminated** at $G$ when $G$ contains the empty clause or has no unit clause.
--
--   These are the operations of Lemma 2.1, the feasibility test used throughout the algorithm.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Lemma 2.1, p.2

import Mathlib
import Definitions.Def_ReadTwiceCount_pFalse

namespace ReadTwiceCount

variable {M : ℕ}

/-- A **unit clause** on the literal `l`: a nonempty clause all of whose literals are `l`. (A
clause such as `(x ∨ x)` is a unit clause on `x`.) -/
def IsUnitClause (C : List (Lit M)) (l : Lit M) : Prop := C ≠ [] ∧ ∀ x ∈ C, x = l

/-- **One step of unit propagation** (He, *A Deterministic Approximation Scheme for Counting
Read-Twice CNF Assignments*, STOC 2027 submission, manuscript sha256 7a2a9dcd…, Lemma 2.1, p.2):
`G` has a unit clause on a literal `l`, and `G'` is `G` with `l` pinned true by substitution. -/
def UPStep (G G' : Formula M) : Prop :=
  ∃ C ∈ G.clauses, ∃ l : Lit M, IsUnitClause C l ∧ G' = G.pinTrue l

/-- **Propagation has terminated** at `G`: `G` has an empty clause, or no unit clause. -/
def UPTerminal (G : Formula M) : Prop :=
  [] ∈ G.clauses ∨ ∀ C ∈ G.clauses, ∀ l : Lit M, ¬IsUnitClause C l

end ReadTwiceCount


