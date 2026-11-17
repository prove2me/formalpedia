-- Prove2me | Definitions.Def_SparseDisc_Supplement_NoTwoNeighboursOnAvoidingCycle
-- name    : SparseDisc_Supplement_NoTwoNeighboursOnAvoidingCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:05:16.037207+00:00
-- url     : https://prove2.me/theorems/f744bb5b-f1a2-4c57-8563-75eeee4cac6b
-- title:
--   No two neighbours on a cycle avoiding the vertex
-- statement:
--   A graph has this property if no vertex $v$ has two distinct neighbours that both lie on one cycle whose vertex set avoids $v$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.22(b), p.38

import Mathlib

namespace SparseDisc.Supplement

/-- No vertex has two distinct neighbours lying on a cycle that avoids it, the graph condition in
Theorem 8.22(b) (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), p.38). -/
def NoTwoNeighboursOnAvoidingCycle {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v a b, a ≠ b → G.Adj v a → G.Adj v b →
    ¬ ∃ p : G.Walk a a, p.IsCycle ∧ b ∈ p.support ∧ v ∉ p.support

end SparseDisc.Supplement


