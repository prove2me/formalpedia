-- Prove2me | Definitions.Def_UniqueOptScores_setOracle
-- name    : UniqueOptScores_setOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:47.435443+00:00
-- url     : https://prove2.me/theorems/7928e256-1e43-41cc-823c-abc6a92b9b1d
-- title:
--   The oracle $A$ as a word function
-- statement:
--   An **oracle** is a language $A \subseteq \{0,1\}^*$, and an oracle machine may ask whether a string $q$ belongs to $A$. For the machine model used throughout this mission (oracle Turing machines whose oracle maps a query word to an answer word) the oracle $A$ answers the query $q$ with the one-bit word
--   $$
--   \mathrm{ans}_A(q) = \begin{cases} 1 & q \in A,\\ 0 & q \notin A.\end{cases}
--   $$
--   Every relativized class of the mission is defined with this answer function.
--
--   **Formalization Note** Strings are lists of Booleans and an oracle is any set of such lists. The reused machine model `HMBinPacking.OracleMachine` takes oracles of type `List Bool → List Bool`; this wrapper turns a language into such a function, deciding `q ∈ A` classically.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2 (Relativization), p.15

import Mathlib

namespace UniqueOptScores

/-- **The oracle `A` as a word function.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.15: "An oracle is a language A ⊆ {0, 1}∗. An oracle machine M^A may query whether
a string belongs to A."

The answer to the query `q` is the one-bit word `[true]` if `q ∈ A` and `[false]` otherwise.

**Formalization Note.** Strings are `List Bool` and an oracle is any `A : Set (List Bool)`. The
reused machine model `HMBinPacking.OracleMachine` takes oracles of type `List Bool → List Bool`;
this wrapper turns a language into such a function (classical decidability of `q ∈ A`). -/
noncomputable def setOracle (A : Set (List Bool)) : List Bool → List Bool :=
  fun q => [@decide (q ∈ A) (Classical.propDecidable _)]

end UniqueOptScores


