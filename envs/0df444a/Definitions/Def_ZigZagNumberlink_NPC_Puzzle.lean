-- Prove2me | Definitions.Def_ZigZagNumberlink_NPC_Puzzle
-- name    : ZigZagNumberlink_NPC_Puzzle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T04:15:01.017256+00:00
-- url     : https://prove2.me/theorems/3b67eae2-c5ba-43f0-9606-a3e83eee0b9d
-- title:
--   Definitions 1–4 — square-board instances, paths, and full-cover solutions
-- statement:
--   A square board has $n$ rows and $n$ columns. A raw puzzle records $n,k\in\mathbb N$ and a label in $\{0,\ldots,k\}$ on each cell; zero marks an unnumbered cell. Validity requires $n>0$ and exactly two distinct cells with each label $1,\ldots,k$. Thus all terminal squares are distinct, and $k$ varies with the input.
--
--   A path is a finite sequence of distinct cells whose successive cells share a side. A solution consists of one such path for each nonzero label, with distinct first and last cells bearing that label, and with every board cell belonging to exactly one path. A puzzle is solvable precisely when it is valid and admits such a family. Paths may bend arbitrarily, run alongside themselves, and use long routes even when their endpoints are adjacent. No extra cycles are included. A positive board with zero pairs is valid but unsolvable.
--
--   The underlying square grid is the published Robertson–Seymour grid definition. Coordinates are zero-based (column,row), translated to the paper by adding one to each coordinate. Numbering terminal pairs and allowing either endpoint order change no instance or solution existence. The square specialization is exactly the domain of Theorem 1; this item does not assert a complexity result for arbitrary rectangles. Empty and singleton lists satisfy the bare path predicate, but cannot be solution paths because endpoints must be distinct.
-- source:
--   Adcock et al., Zig-Zag Numberlink is NP-Complete, Journal of Information Processing 23(3), 239–245 (2015), https://doi.org/10.2197/ipsjjip.23.239, Definitions 1–4, printed p. 240 / PDF p. 2; square specialization in Theorem 1, printed p. 241 / PDF p. 3. PDF SHA-256: 7686eee342d84716ae6a65b1b061d92002874689610ad4478f5aeed7406b5daf.

import Definitions.Def_RobertsonSeymour1986_GM5_grid

namespace ZigZagNumberlink.NPC

/-- Coordinates are (column,row), starting at zero. -/
abbrev Cell (n : ℕ) := Fin n × Fin n

/-- Raw square-board data; label zero means no terminal. -/
structure Puzzle where
  n : ℕ
  k : ℕ
  label : Cell n → Fin (k + 1)

/-- Positive board size and exactly two cells bearing each nonzero label. -/
def Puzzle.Valid (F : Puzzle) : Prop :=
  0 < F.n ∧ ∀ i : Fin F.k,
    ∃ a b : Cell F.n, a ≠ b ∧
      ∀ v : Cell F.n, (F.label v).val = i.val + 1 ↔ v = a ∨ v = b

/-- A simple ordered path: no repeated cells and orthogonal successive steps. -/
def IsPath {n : ℕ} (p : List (Cell n)) : Prop :=
  p.Nodup ∧ p.IsChain (RobertsonSeymour1986.GM5.grid n).Adj

/-- One path for each terminal label, with every cell on exactly one path. -/
def Puzzle.IsSolution (F : Puzzle) (paths : Fin F.k → List (Cell F.n)) : Prop :=
  (∀ i, IsPath (paths i) ∧
    ∃ a b : Cell F.n,
      (paths i).head? = some a ∧ (paths i).getLast? = some b ∧ a ≠ b ∧
      (F.label a).val = i.val + 1 ∧ (F.label b).val = i.val + 1) ∧
  (∀ v : Cell F.n, ∃! i : Fin F.k, v ∈ paths i)

/-- Solvability is computed from the puzzle data, with validity checked explicitly. -/
def Puzzle.Solvable (F : Puzzle) : Prop :=
  F.Valid ∧ ∃ paths : Fin F.k → List (Cell F.n), F.IsSolution paths

end ZigZagNumberlink.NPC


