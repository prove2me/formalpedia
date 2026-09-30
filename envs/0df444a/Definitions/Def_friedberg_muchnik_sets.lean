-- Prove2me | Definitions.Def_friedberg_muchnik_sets
-- name    : friedberg_muchnik_sets
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-09T19:38:17.104566+00:00
-- url     : https://prove2.me/theorems/9b04ea71-082a-46e3-8b72-f1a30a524cc5
-- title:
--   Computably enumerable sets and total Turing oracles
-- statement:
--   Let $A,B\subseteq\mathbb N$, where $0\in\mathbb N$. A set is computably enumerable when there is a partial recursive procedure that halts exactly on its members. A set is computable when its membership predicate has a total computable Boolean decision function.
--
--   The total characteristic-function oracle for $A$ is
--
--   $$\chi_A(n)=\begin{cases}1&n\in A,\\0&n\notin A.\end{cases}$$
--
--   Define $A\le_T B$ by partial recursiveness of $\chi_A$ relative to oracle $\chi_B$. Both characteristic functions are defined on every natural input. Define Turing equivalence by reducibility in both directions, and define Turing incomparability by nonreducibility in both directions. The degree of a set is the equivalence class of its characteristic-function oracle in the quotient of partial functions by mutual Turing reducibility. A degree is computably enumerable when it is represented by a computably enumerable set.
--
--   These definitions provide the set and oracle interface for the existence theorem. They impose no computability assumption on an arbitrary oracle set.
--
--   **Formalization Note** This bundle preserves the eight supplied definitions in namespace `Computability`. `PFun.lift` embeds the total natural-number-valued characteristic function into the partial-function type used by Mathlib; the `noncomputable` marker allows its definition for arbitrary sets and does not imply that the oracle is computable.
-- source:
--   User-supplied Lean definitions using Mathlib REPred, ComputablePred, TuringReducible, and TuringDegree; mathematical context: Richard M. Friedberg (1957), Two recursively enumerable sets of incomparable degrees of unsolvability (solution of Post's problem, 1944), PNAS 43(2), 236–238. DOI: https://doi.org/10.1073/pnas.43.2.236; free archive: https://pmc.ncbi.nlm.nih.gov/articles/PMC528418/. Exact two-set statement and working proof reference: Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, statement p. 51, proof pp. 51–54: https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf#page=51. Earlier independent contribution: A. A. Muchnik (1956), On the unsolvability of the problem of reducibility in the theory of algorithms, Doklady Akademii Nauk SSSR 108(2), 194–197 (Russian); Math-Net bibliography: https://www.mathnet.ru/rus/person46479.

import Mathlib.Computability.RE
import Mathlib.Computability.TuringDegree

open scoped Computability

namespace Computability

/-- A set of naturals is computably enumerable (c.e., r.e.). -/
def CEnumerable (A : Set ℕ) : Prop :=
  REPred (fun n : ℕ => n ∈ A)

/-- A set of naturals is computable/recursive/decidable. -/
def ComputableSet (A : Set ℕ) : Prop :=
  ComputablePred (fun n : ℕ => n ∈ A)

/-- The total characteristic function, represented as a partial-function oracle. -/
noncomputable def setOracle (A : Set ℕ) : ℕ →. ℕ := by
  classical
  exact PFun.lift (fun n : ℕ => if n ∈ A then 1 else 0)

/-- Turing reducibility between the total characteristic-function oracles. -/
def SetTuringReducible (A B : Set ℕ) : Prop :=
  setOracle A ≤ᵀ setOracle B

/-- Two sets have the same Turing degree. -/
def SetTuringEquivalent (A B : Set ℕ) : Prop :=
  SetTuringReducible A B ∧ SetTuringReducible B A

/-- Two sets have incomparable Turing degrees. -/
def TuringIncomparable (A B : Set ℕ) : Prop :=
  ¬ SetTuringReducible A B ∧
  ¬ SetTuringReducible B A

/-- The Turing degree of the total characteristic-function oracle. -/
noncomputable def degreeOfSet (A : Set ℕ) : TuringDegree :=
  toAntisymmetrization TuringReducible (setOracle A)

/-- A Turing degree is c.e. if it contains a c.e. set. -/
def CEnumerableDegree (d : TuringDegree) : Prop :=
  ∃ A : Set ℕ,
    CEnumerable A ∧ degreeOfSet A = d

end Computability


