-- Prove2me | Definitions.Def_SparseDisc_BlockDegreeLE
-- name    : SparseDisc_BlockDegreeLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:10.512394+00:00
-- url     : https://prove2.me/theorems/dcc243aa-af6d-4175-89b0-91f6dfaddbc5
-- title:
--   Every block has maximum degree at most $\Delta$
-- statement:
--   A graph $H$ has **block degree at most $\Delta$** if every block of $H$ has maximum degree at most $\Delta$: for every block $B$ and every vertex $v$ of $B$, $v$ has at most $\Delta$ neighbours inside $B$.
--
--   This hypothesis appears in Theorem 1.9(c): a function may have large degree in $H$ as long as its degree inside each block is small.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9(c), p.5; Corollary 8.34(iii), p.44

import Mathlib
import Definitions.Def_SparseDisc_IsBlock

namespace SparseDisc

open Classical in
/-- `BlockDegreeLE H Δ`: **every block of `H` has maximum degree at most `Δ`** — within each block,
every vertex has at most `Δ` neighbours in that block (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy
Beyond Additive Functions*, STOC 2027 submission manuscript (sha256 0f09ec60…25b81), Theorem 1.9(c),
p.5, and Corollary 8.34(iii), p.44). -/
def BlockDegreeLE {V : Type} [DecidableEq V] (H : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ W : Finset V, IsBlock H W → ∀ v ∈ W, (W.filter (fun w => H.Adj v w)).card ≤ Δ

end SparseDisc


