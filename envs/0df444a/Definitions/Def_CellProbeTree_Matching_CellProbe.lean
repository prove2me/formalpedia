-- Prove2me | Definitions.Def_CellProbeTree_Matching_CellProbe
-- name    : CellProbeTree_Matching_CellProbe
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:27.421912+00:00
-- url     : https://prove2.me/theorems/d812f804-c87f-42ce-8c1c-85c52a71098c
-- title:
--   Static cell-probe structures for findopen/findclose on Dyck words
-- statement:
--   Let $\mathcal D_n$ be the set of **Dyck words** of semilength $n$: words with $n$ openings and $n$ closings in which every prefix has at least as many openings as closings (Mathlib's `DyckWord` with `semilength = n`); $|\mathcal D_n| = C_n = \binom{2n}{n}/(n+1)$, the Catalan number. Put $N = 2n$.
--
--   A **static cell-probe structure** with $s$ cells of $w$ bits for $\mathcal D_n$ consists of
--   * an **encoding** $\mathrm{Enc} : \mathcal D_n \to (\{0,1\}^w)^s$, an arbitrary function (non-systematic: the whole input may be encoded arbitrarily), and
--   * for each position $i \in [N]$, a deterministic, fully adaptive **query algorithm**: a finite tree whose inner nodes name a cell address in $[s]$ and branch on the full $w$-bit content read there, and whose leaves output a position. The algorithm receives only $i$ (no bracket-type flag).
--
--   It is **correct** when, for every $X \in \mathcal D_n$ and every $i$, running the tree for $i$ on the memory $\mathrm{Enc}(X)$ returns the mate of $i$ in $X$ ($\mathrm{findclose}_X(i)$ at an opening, $\mathrm{findopen}_X(i)$ at a closing). It makes **at most $t$ probes** when every such run reads at most $t$ cells. Computation is free; the space is $s\cdot w$ bits.
--
--   **Formalization Note.** Memory is `Fin s → BitVec w`; the query trees are `DynOracleConn.ProbeTree (Fin s) (BitVec w) (Fin (2 * n))` (published definition), and the probe count is its `cost`, which counts every probe on the path taken. Positions are 0-based (`Fin (2 * n)`). There is no condition on $s$ (any number of cells, possibly $0$) and none on the encoding (injectivity follows from correctness).
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), p. 4, §1.2 (model) and Theorem 1.2

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree
import Definitions.Def_CellProbeTree_Matching_Mate

/-!
# Static cell-probe data structures for findopen/findclose

Liang, Liu, *Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality*,
STOC 2027 submission, §1.2 (p. 4) and Theorem 1.2.

A structure for Dyck words of semilength `n` with `s` cells of `w` bits consists of an arbitrary
(non-systematic) encoding of each Dyck word into the memory `Fin s → BitVec w`, and, for every
position `i`, a deterministic fully adaptive probe tree (`DynOracleConn.ProbeTree`): each inner
node reads one cell, the next step depends on the full `w`-bit content read, and each leaf outputs
a position. The tree for `i` receives only `i`.

**Formalization Note.** Positions are 0-based (`Fin (2 * n)`). The probe count is
`DynOracleConn.ProbeTree.cost`, which counts every probe on the path taken (a repeated read of the
same cell counts again).
-/

namespace CellProbeTree.Matching

open DynOracleConn

/-- Dyck words of semilength `n` (the paper's `D_n`). -/
abbrev DyckSet (n : ℕ) := {X : DyckWord // X.semilength = n}

/-- A static cell-probe structure on `DyckSet n`: `s` cells of `w` bits, an arbitrary encoding,
and one adaptive probe tree per position (0-based), answering a position. -/
structure MatchingStructure (n s w : ℕ) where
  /-- The memory contents stored for each Dyck word: any function at all. -/
  enc : DyckSet n → (Fin s → BitVec w)
  /-- The query algorithm for position `i`; it receives only `i`. -/
  query : Fin (2 * n) → ProbeTree (Fin s) (BitVec w) (Fin (2 * n))

namespace MatchingStructure

variable {n s w : ℕ}

/-- Exactness on every input: on every Dyck word `X` of semilength `n`, the tree for position `i`
returns the mate of `i` (findclose at an opening, findopen at a closing). -/
def Correct (D : MatchingStructure n s w) : Prop :=
  ∀ (X : DyckSet n) (i : Fin (2 * n)),
    Mate X.1.toList i.1 (ProbeTree.run (D.query i) (D.enc X)).1

/-- Worst-case query time: every query on every input makes at most `t` probes. -/
def ProbesAtMost (D : MatchingStructure n s w) (t : ℕ) : Prop :=
  ∀ (X : DyckSet n) (i : Fin (2 * n)), ProbeTree.cost (D.query i) (D.enc X) ≤ t

end MatchingStructure

end CellProbeTree.Matching


