-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage
-- name    : ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:16.744128+00:00
-- url     : https://prove2.me/theorems/ff290a76-f268-4997-a32c-b0e3754b5036
-- title:
--   Grid stream $\Sigma$: columns held by a set and the columns of a stage
-- statement:
--   The definitions concern the coverage stream $\Sigma = A \circ B_1 \circ \dots \circ B_m$ of Appendix B.1.1 for the budget $k$, whose elements are the stream positions $0, \dots, k + mk - 1$ (the type `Fin (k + m * k)`). The first $k$ positions are the row sets $a_1,\dots,a_k$; stage $j \ge 1$ occupies the positions $jk, \dots, jk + k - 1$ and presents the column sets $b_{1,j},\dots,b_{k,j}$.
--
--   - `ConsistentSubmodular.GridStream.columnsHeld` $(k, S)$: for a set $S$ of stream positions, the number of column sets it contains,
--   $$|\{e \in S : e \ge k\}|,$$
--   that is, the elements of $S$ whose position is at least $k$ (all elements that are not row sets).
--   - `ConsistentSubmodular.GridStream.stageColumns` $(k, m, j)$: the set of positions $e$ with $jk \le e < (j+1)k$, i.e. the $k$ sets arriving at positions $jk + i$, $i < k$. For $j \ge 1$ these are the columns $b_{1,j},\dots,b_{k,j}$ of stage $j$ (for $j = 0$ the same window is the block of rows).
--
--   These definitions are the column-side counterparts of `rowsHeld` and serve the bookkeeping in the impossibility argument for deterministic algorithms on the grid stream $\Sigma$ (Section 3.1 and Appendix B.1): they let one count how many of the $k$ retained sets are columns and how many columns of a given stage are held.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

/-- The number of column sets `b_{i,j}` in `S`. -/
def columnsHeld (k : ℕ) {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (S.filter fun e => k ≤ e.val).card

/-- The columns `b_{1,j}, ..., b_{k,j}` of stage `j`, at the stream positions
`j k + i` with `i < k`. -/
def stageColumns (k m j : ℕ) : Finset (Fin (k + m * k)) :=
  univ.filter fun e => j * k ≤ e.val ∧ e.val < (j + 1) * k

end ConsistentSubmodular.GridStream

end


