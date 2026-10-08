-- Prove2me | Definitions.Def_BinaryMatching
-- name    : BinaryMatching
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:01.877774+00:00
-- url     : https://prove2.me/theorems/f689cb26-8b51-46d2-bb56-94146b8768c0
-- statement:
--   A loopless graph consists of an edge set with two endpoint maps into its vertex set, with distinct endpoints for every edge; parallel edges are allowed. For finite vertex and edge sets, a vertex is incident to an edge when it equals either endpoint, and a perfect matching is a set of edges containing exactly one incident edge at every vertex. The collection of perfect matchings is finite. For a nonnegative integer n, the complete graph has vertices 0, …, n−1 and one edge (i,j) for each i<j. A binary-matching input contains n and a list of records, each specifying two natural-number endpoints and a natural-number multiplicity. Its required validity conditions are 0≤left<right<n and no repeated endpoint pair; multiplicities may be zero. An edge receives the multiplicity of its record, or zero if absent. The matching count is the sum, over all perfect matchings of the complete graph, of the product of their edge multiplicities, thus counting choices of parallel edges in the represented graph. To encode a natural number as Booleans, write one false for each bit of its binary representation, then true, then those bits. A record concatenates the encodings of its left endpoint, right endpoint, and multiplicity. An input concatenates the encodings of n, the number of records, and all records in list order.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BinaryMatching.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BinaryMatching.lean; bytes 16..1918
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u_1 u_2

namespace MatchingEntropy

structure LooplessGraph (V : Type u_1) (E : Type u_2) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

namespace LooplessGraph

variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e=v ∨ G.right e=v
def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e∈M ∧ G.Incident v e
abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}
noncomputable instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _

end LooplessGraph

end MatchingEntropy

namespace BinaryMatching

abbrev Pair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}
def completeGraph (n : ℕ) : MatchingEntropy.LooplessGraph (Fin n) (Pair n) where
  left e := e.val.1
  right e := e.val.2
  loopless e := ne_of_lt e.property

structure Record where
  left : ℕ
  right : ℕ
  multiplicity : ℕ
  deriving DecidableEq

structure Input where
  n : ℕ
  records : List Record
  valid : ∀ e∈records, e.left < e.right ∧ e.right < n
  unique : (records.map (fun e => (e.left,e.right))).Nodup

def multiplicity (G : Input) (e : Pair G.n) : ℕ :=
  match G.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
  | none => 0
  | some r => r.multiplicity

noncomputable def count (G : Input) : ℕ :=
  ∑ M : (completeGraph G.n).Matching, ∏ e∈M.val, multiplicity G e

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length false ++ true :: n.bits

def encodeRecord (r : Record) : List Bool :=
  encodeNat r.left ++ encodeNat r.right ++ encodeNat r.multiplicity

def encodeInput (G : Input) : List Bool :=
  encodeNat G.n ++ encodeNat G.records.length ++ G.records.flatMap encodeRecord



end BinaryMatching
end OAI


