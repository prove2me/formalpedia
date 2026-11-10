-- Prove2me | Definitions.Def_ExactOneHS_Counting_ExclusionCoverage
-- name    : ExactOneHS_Counting_ExclusionCoverage
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:11:28.790195+00:00
-- url     : https://prove2.me/theorems/e6bf689f-8d34-4d06-bd4b-3a69cc15f7a4
-- title:
--   The pairwise-exclusion and coverage formula $B \wedge C_1 \wedge \dots \wedge C_h$ of Eqs. (16)–(17)
-- statement:
--   Let $S_1, \dots, S_h$ be subsets of $[r]$. Let $E$ be the set of unordered pairs $\{u, v\}$ of distinct elements that occur together in at least one $S_j$. Define, on the $r$ declared variables $x_1, \dots, x_r$,
--   $$B(x) := \bigwedge_{\{u,v\} \in E} (\neg x_u \vee \neg x_v), \qquad C_j(x) := \bigvee_{i \in S_j} x_i \quad (j \in [h]),$$
--   and the CNF $B \wedge C_1 \wedge \dots \wedge C_h$, whose model count is taken over all $2^r$ assignments of the $r$ declared variables, including those that occur in no clause.
--
--   **Formalization Note.** Elements are `Fin r`; an unordered pair is written as $(u, v)$ with $u < v$; the formula is the finite set of clauses $\{\neg x_u, \neg x_v\}$ ($\{u,v\} \in E$) together with the clauses $C_j$, so repeated clauses collapse, which does not change the formula's truth value.
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 15, proof of Theorem 1.2, Eqs. (16), (17)

import Mathlib
import Definitions.Def_SubexponentialSAT

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- `E`: the unordered pairs `{u, v}` (written `u < v`) of distinct elements occurring together
in at least one of the sets `S`. -/
def exclusionPairs {r : ℕ} (S : List (Finset (Fin r))) : Finset (Fin r × Fin r) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ ∃ T ∈ S, p.1 ∈ T ∧ p.2 ∈ T

/-- `B = ⋀_{{u,v} ∈ E} (¬x_u ∨ ¬x_v)` (Eq. (16)). -/
def exclusionCNF {r : ℕ} (S : List (Finset (Fin r))) : SAT.CNF (Fin r) :=
  (exclusionPairs S).image fun p => {⟨p.1, false⟩, ⟨p.2, false⟩}

/-- The coverage clause `C_j = ⋁_{i ∈ S_j} x_i` (Eq. (16)). -/
def coverageClause {r : ℕ} (T : Finset (Fin r)) : SAT.Clause (Fin r) :=
  T.image fun i => ⟨i, true⟩

/-- The formula `B ∧ C_1 ∧ ⋯ ∧ C_h` of Eq. (17) for the sets `S = (S_1, …, S_h)`, on all `r`
declared variables `Fin r`. -/
def exclusionCoverage {r : ℕ} (S : List (Finset (Fin r))) : SAT.CNF (Fin r) :=
  exclusionCNF S ∪ S.toFinset.image coverageClause

end ExactOneHS.Counting


