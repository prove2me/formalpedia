-- Prove2me | Definitions.Def_AssadiSemiStreaming_Greedy_MatchingStream
-- name    : AssadiSemiStreaming_Greedy_MatchingStream
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:39:11.421209+00:00
-- url     : https://prove2.me/theorems/4e63c2a7-0537-47c4-a944-2c2e3cb025c9
-- title:
--   Matching-output streams and semi-streaming space
-- statement:
--   Specialize the generic machine to unordered vertex pairs as input and finite sets of unordered vertex pairs as output. A stream is a duplicate-free enumeration of all the edges of a finite simple graph on n labeled vertices. The hard subclass consists of bipartite graphs with a perfect matching. Use the published ordinary matching, perfect-matching, and maximum-cardinality definitions. An output succeeds at ratio r precisely when it is the image of a graph-edge matching M and |M| ≥ r ν(G). Thus loops, nonexistent edges, and shared endpoints cause failure; machines capable of such outputs are still included. Success probability is the finite sum of output masses over this event. A space function is semi-streaming when there exist B>0, a natural exponent k, and a threshold N such that s(n) ≤ B n (log₂(n+2))^k for all n≥N. None of these definitions asserts a lower bound.
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), §1, printed p. 1 / PDF 3; Theorem 2 and footnotes 6–7, printed p. 6 / PDF 8

import Definitions.Def_AssadiSemiStreaming_Greedy_StreamingMachine
import Definitions.Def_CatalyticMatching_General_Matching
open scoped ENNReal

namespace AssadiSemiStreaming.Greedy

abbrev MatchingMachine (n s : ℕ) :=
  StreamingMachine (Sym2 (Fin n)) (Finset (Sym2 (Fin n))) s

/-- A simple insertion stream contains each edge of G exactly once, in any order. -/
def IsEdgeStream {n : ℕ} (G : SimpleGraph (Fin n)) (stream : List (Sym2 (Fin n))) : Prop :=
  stream.Nodup ∧ ∀ e, e ∈ stream ↔ e ∈ G.edgeSet

/-- The hard subclass: bipartite graphs admitting a perfect matching. -/
def HardGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∃ color : Fin n → Bool, ∀ u v, G.Adj u v → color u ≠ color v) ∧
  ∃ M : Finset G.edgeSet, MulmuleyVV.Matching.IsPerfectMatchingEdges G M

/-- Invalid output is failure, rather than an excluded kind of machine. -/
noncomputable def MatchingSuccess {n s : ℕ} (A : MatchingMachine n s)
    (G : SimpleGraph (Fin n)) (stream : List (Sym2 (Fin n))) (ratio : ℝ) : ℝ≥0∞ := by
  classical
  exact ∑ out : Finset (Sym2 (Fin n)),
    if (∃ M : Finset G.edgeSet, CatalyticMatching.General.IsMatching M ∧
      M.image (fun e => (e : Sym2 (Fin n))) = out ∧
      ratio * (CatalyticMatching.General.matchingNumber G : ℝ) ≤ (M.card : ℝ))
    then A.law stream out else 0

/-- Constants in a semi-streaming bound are fixed before the input size. -/
def SemiStreamingSpace (s : ℕ → ℕ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∃ k N : ℕ, ∀ n ≥ N,
    (s n : ℝ) ≤ B * n * (Real.log (n + 2) / Real.log 2) ^ k

end AssadiSemiStreaming.Greedy


