-- Prove2me | Definitions.Def_JohnsonApprox_Shared_Problem
-- name    : JohnsonApprox_Shared_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:20:13.345098+00:00
-- url     : https://prove2.me/theorems/ade461da-f5f0-4952-9a91-baccede7bfa0
-- title:
--   MAXIMUM SATISFIABILITY: literals, clauses, truth assignments, S* and MS(k) (Section 4)
-- statement:
--   This file sets up the MAXIMUM SATISFIABILITY problem of Johnson (1974), Section 4, in the words of the paper: "Let $L = \bigcup_{i>0}\{x_i, \bar x_i\}$ be a set of literals. A clause will be any finite subset $C \subseteq L$. A truth assignment will be any subset $T \subseteq L$ such that for no $i > 0$ is $\{x_i, \bar x_i\} \subseteq T$. Truth assignment $T$ satisfies clause $C$ if $C \cap T \neq \emptyset$."
--
--   1. A **literal** is a variable $x_i$ or its negation $\bar x_i$; the **complement** of a literal swaps the two ($\bar{\bar x}_i = x_i$).
--   2. A **clause** is a finite set of literals. It may contain both $x_i$ and $\bar x_i$.
--   3. A **truth assignment** is any set $T$ of literals that contains no complementary pair. It need not assign every variable.
--   4. $T$ **satisfies** $C$ when $C$ and $T$ share a literal.
--
--   An input of MS is a finite set $S = \{C_1, \dots, C_p\}$ of clauses. Its feasible solutions are
--   $$\mathrm{SOL}_{MS}(S) = \{S' \subseteq S : \text{some truth assignment } T \text{ satisfies every } C \in S'\},$$
--   measured by $m_{MS}(S') = |S'|$, and the optimal measure is
--   $$S^* = \max\{|S'| : S' \in \mathrm{SOL}_{MS}(S)\}.$$
--   The empty subset is always feasible, so the maximum is over a finite nonempty family. Finally, "MS(k) will denote the subproblem with inputs restricted to sets of clauses, each clause of which contains at least $k$ distinct elements": $S \in MS(k)$ iff $|C| \geq k$ for every $C \in S$.
--
--   These are the objects about which Theorem 2 (algorithm B1) and Theorem 3 (algorithm B2) are stated. This one definition serves chunk 02-maxsat-greedy (p. 262, Section 4; Theorem 2 and its proof, pp. 262–263, including the $k = 3$ example of p. 263) and chunk 03-maxsat-weighted (p. 262, Section 4; Theorem 3 and its proof, pp. 263–264, including the $k = 3$ example of p. 264).
--
--   **Formalization Note** Variables are indexed by all natural numbers (the paper uses $i > 0$; the index set is immaterial). A truth assignment is a `Set` of literals with no complementary pair, so it is partial, as in the paper. $S^*$ is `Finset.sup'` of the cardinality over the finite, nonempty family `solutions S`; the lemma `empty_mem_solutions` supplies nonemptiness. An input is a `Finset` of clauses, hence a set without duplicates, as on the page. The page prints "$\mathrm{SOL}_{MS}(T)$" for $\mathrm{SOL}_{MS}(S)$, a typo.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 262, Section 4 (MAXIMUM SATISFIABILITY); pp. 258–259, Section 2

import Mathlib

namespace JohnsonApprox.Shared

/-- A literal: the variable `x_var` if `pos = true`, its negation `x̄_var` if `pos = false`.
Variables are indexed by natural numbers (the paper indexes them by `i > 0`; any index set of
the same cardinality gives the same problem). -/
structure Literal where
  var : ℕ
  pos : Bool
  deriving DecidableEq

/-- The complementary literal: `x̄` of `x`, and `x` of `x̄` (so `neg (neg l) = l`). -/
def Literal.neg (l : Literal) : Literal := ⟨l.var, !l.pos⟩

/-- A clause is any finite set of literals. -/
abbrev Clause := Finset Literal

/-- A truth assignment is any set `T` of literals containing no complementary pair
`{x_i, x̄_i}`. It may leave variables unassigned. -/
def Assignment := {T : Set Literal // ∀ l ∈ T, l.neg ∉ T}

/-- Truth assignment `T` satisfies clause `C` if `C ∩ T ≠ ∅`. -/
def satisfies (T : Assignment) (C : Clause) : Prop := ∃ l ∈ C, l ∈ T.1

/-- A set of clauses is satisfiable if one truth assignment satisfies every clause in it. -/
def Satisfiable (S' : Finset Clause) : Prop := ∃ T : Assignment, ∀ C ∈ S', satisfies T C

open Classical in
/-- The feasible solutions `SOL_MS(S)`: the subsets `S' ⊆ S` satisfied by one truth assignment. -/
noncomputable def solutions (S : Finset Clause) : Finset (Finset Clause) :=
  S.powerset.filter Satisfiable

/-- The empty subset is always feasible (it is satisfied by the empty assignment). -/
theorem empty_mem_solutions (S : Finset Clause) : ∅ ∈ solutions S := by
  classical
  unfold solutions
  rw [Finset.mem_filter]
  refine ⟨Finset.empty_mem_powerset S, ⟨⟨∅, fun l hl => absurd hl (Set.notMem_empty l)⟩, ?_⟩⟩
  intro C hC
  exact absurd hC (Finset.notMem_empty C)

/-- The optimal measure `S* = MAX{|S'| : S' ∈ SOL_MS(S)}`, a maximum over a finite nonempty set. -/
noncomputable def opt (S : Finset Clause) : ℕ :=
  (solutions S).sup' ⟨∅, empty_mem_solutions S⟩ Finset.card

/-- `S` is an input of `MS(k)`: every clause of `S` contains at least `k` distinct literals. -/
def InMS (k : ℕ) (S : Finset Clause) : Prop := ∀ C ∈ S, k ≤ C.card

end JohnsonApprox.Shared


