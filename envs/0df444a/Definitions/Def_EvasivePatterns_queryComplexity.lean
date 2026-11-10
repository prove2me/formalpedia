-- Prove2me | Definitions.Def_EvasivePatterns_queryComplexity
-- name    : EvasivePatterns_queryComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:01.770376+00:00
-- url     : https://prove2.me/theorems/d1bc7b56-ee5f-4484-bdf0-5eab88dc3355
-- title:
--   Deterministic query complexity $D_P(n)$ of deciding whether $P$ occurs
-- statement:
--   For a pattern $P$ and a text length $n$, $D_P(n)$ is the smallest number $d$ such that some **adaptive deterministic decision tree** decides, for every text $X \in \{0,1\}^n$, whether $P$ occurs in $X$, and reads at most $d$ positions of $X$ on every input. At each internal node the tree reads one text position and branches on the bit it sees; at a leaf it answers yes or no. Computation between queries is free, so only the number of positions read is counted.
--
--   Always $D_P(n) \le n$. A pattern is called eventually evasive when $D_P(n) = n$ for all sufficiently large $n$.
--
--   **Formalization Note** The algorithms are the published decision trees `QAlgorithms.DecisionTree (Fin n) Bool Bool` with `eval` and `MakesAtMost`. $D_P(n)$ is the infimum of the admissible worst-case bounds; this set is nonempty (the tree reading every position), so the infimum is attained.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §1, p.1 (PDF p.2), lines 3–7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_EvasivePatterns_occurs

namespace EvasivePatterns

/-- **Deterministic query complexity `D_P(n)` of pattern matching.** The smallest number `d` such
that some adaptive deterministic decision tree on the text positions `Fin n`, branching on the bit
read, computes the occurrence function `f_{P,n}` on every text `X ∈ {0,1}^n` and reads at most `d`
positions on every text.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §1, printed p. 1 (PDF p. 2), lines 3–7: "The pattern P ∈ {0, 1}^m
is known in advance; the text X ∈ {0, 1}^n is unknown, and an algorithm may choose which position to
inspect next based on the bits already seen. All computation between queries is free. We denote by
D_P(n) the smallest possible number of queries in the worst case."

**Formalization Note** Algorithms are the published `QAlgorithms.DecisionTree (Fin n) Bool Bool`
(a node queries a position and branches on its bit, a leaf outputs the answer; computation between
queries is free), with `eval` its output and `MakesAtMost d` the worst-case bound on the number of
queries along the path a text follows. `D_P(n)` is the infimum (`sInf` in `ℕ`) of the admissible
bounds; the set is nonempty for every `n` (the tree that reads all `n` positions), so the infimum is
attained and is at most `n`. -/
noncomputable def queryComplexity (P : List Bool) (n : ℕ) : ℕ :=
  sInf {d : ℕ | ∃ T : QAlgorithms.DecisionTree (Fin n) Bool Bool,
    (∀ X : Fin n → Bool, T.eval X = decide (occurs P X)) ∧ T.MakesAtMost d}

end EvasivePatterns


