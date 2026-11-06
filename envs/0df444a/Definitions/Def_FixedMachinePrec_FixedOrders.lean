-- Prove2me | Definitions.Def_FixedMachinePrec_FixedOrders
-- name    : FixedMachinePrec_FixedOrders
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:08.681487+00:00
-- url     : https://prove2.me/theorems/cb73af7b-4a3a-4cdd-a2be-cba47ed9bb91
-- title:
--   The fixed orders: incidence-vector order $b_N\cdots b_1$, lexicographic $m$-subsets, smallest-identifier topological rank
-- statement:
--   All choices of the algorithm are fixed by explicit orders on job sets.
--
--   1. A set $X\subseteq J$ has incidence vector $b_N\cdots b_1$ ($b_j=1$ iff job $j\in X$). Sets are ordered lexicographically by this vector, equivalently by the integer $\sum_j b_j2^{j-1}$; rows of the family table are ordered by the pair $(|X|,\,b_N\cdots b_1)$.
--   2. $m$-subsets of $J$ are ordered by their increasing lists of job labels, compared lexicographically.
--   3. The **smallest-identifier topological order** is obtained by repeatedly removing the smallest label among the available minimal jobs; its **rank** is the position of a job in this order, a value in $\{1,\dots,N\}$.
--
--   These orders determine the atomic list of Algorithm 1, the traversal of cuts and marked slots in Algorithm 3, the processing order of Algorithm 4, and the rank suffixes $R_h$.
--
--   **Formalization Note** Labels are 0-based (`Fin N`), so the integer value is $\sum_{j\in X}2^{j}$; the shift preserves all orders. The sorted list of a family is produced by scanning all integer codes in increasing order, which needs no choice.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §2.2, p.4; §3.1, p.7; §3.2, p.10

import Mathlib

namespace FixedMachinePrec

/-- **The fixed orders that determine every choice of the algorithm.**
Jansen, *Precedence Constraint Scheduling on a Fixed Number of Machines* (manuscript, sha256
08cdf3e1…), §3.1, p.7: "Fix job labels 1, . . . , N. If b_j indicates membership of job j, order
incidence vectors lexicographically as b_N · · · b_1, with 0 < 1; equivalently, order their integer
values ∑_j b_j 2^{j−1}. … Order m-subsets by their increasing lists of job labels."

`code S = ∑_{j ∈ S} 2^j` is the integer value of the incidence vector of `S ⊆ Fin N` (the paper's
`∑ b_j 2^{j−1}` with 0-based labels), so ordering by `code` is the lexicographic order of
`b_N ⋯ b_1`.

**Formalization Note** Job labels are 0-based (`Fin N`); all orders are the paper's after the
shift `j ↦ j − 1`, which preserves them. -/
def code {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  ∑ j ∈ S, 2 ^ (j : ℕ)

/-- The subset of `Fin N` whose incidence vector has integer value `c`. -/
def decodeSet (N c : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun j => c.testBit j

/-- The members of a family of subsets of `Fin N`, listed in increasing `code`, i.e. in the
lexicographic vector order `b_N ⋯ b_1` (§3.1, p.7). -/
def listByCode {N : ℕ} (F : Finset (Finset (Fin N))) : List (Finset (Fin N)) :=
  (List.range (2 ^ N)).filterMap fun c => if decodeSet N c ∈ F then some (decodeSet N c) else none

/-- The members of `F` sorted by the pair `(|X|, b_N ⋯ b_1)` (§3.1, p.7; Algorithm 4, Step 1, p.9):
by cardinality, and by `code` within one cardinality. -/
def listByCardCode {N : ℕ} (F : Finset (Finset (Fin N))) : List (Finset (Fin N)) :=
  (List.range (N + 1)).flatMap fun k => (listByCode F).filter fun X => X.card = k

/-- The `m`-subsets of `Fin N` ordered by their increasing lists of job labels, compared
lexicographically ("Order m-subsets by their increasing lists of job labels", p.7; "for each m-set
A in lexicographic identifier order", Algorithm 1, p.5). -/
def mSubsetsLex (N m : ℕ) : List (Finset (Fin N)) :=
  ((((List.finRange N).sublistsLen m).mergeSort fun a b => decide (a ≤ b))).map List.toFinset

/-- **The smallest-identifier topological order** (§2.2, p.4: "Choose one topological ordering by
repeatedly removing the smallest identifier among available minimal jobs"; §3.2, p.10): `N`
rounds, each appending the smallest label not yet listed all of whose predecessors are listed. -/
def topoList {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] : List (Fin N) :=
  (List.range N).foldl
    (fun l _ =>
      match (List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, prec y x → y ∈ l)) with
      | some x => l ++ [x]
      | none => l)
    []

/-- The rank of that order, `rank : J → {1, …, N}` (1-based position in `topoList`). -/
def topoRank {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (x : Fin N) : ℕ :=
  (topoList prec).idxOf x + 1

end FixedMachinePrec


