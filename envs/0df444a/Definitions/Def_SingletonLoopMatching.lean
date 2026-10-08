-- Prove2me | Definitions.Def_SingletonLoopMatching
-- name    : SingletonLoopMatching
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:54.313302+00:00
-- url     : https://prove2.me/theorems/fce5fc05-e280-400f-ab9b-d7737c3f669c
-- statement:
--   A multigraph is encoded by a number of vertices n and a list of records (left, right, multiplicity) of natural numbers; validity requires left<right<n for every record and that no pair (left,right) repeats. The multiplicity of a pair (i,j) with i<j in Fin n is the multiplicity of its record, or 0 if absent. A loop-augmented input adds to such an ordinary input a list of loop records (vertex, multiplicity), with each vertex less than n and no vertex repeated; the loop multiplicity of a vertex is its record's multiplicity, or 0 if absent. Pairs are the edges of the complete graph on Fin n, and a partial matching is a set of pairs in which no vertex is incident to two distinct members. For a partial matching M, loopVertices(M) is the set of vertices not incident to any edge of M, and its weight is the product of the ordinary multiplicities over the edges of M times the product of loop multiplicities over loopVertices(M). The count of an input is the sum of this weight over all partial matchings of Fin n. Binary encodings are given: a natural number m is written as a run of false of length equal to the number of binary digits of m, then true, then those digits; records, the input and a pair of naturals (the output) are encoded by concatenation, with the lengths of the record lists included. FullEndpoint is a defined proposition, not an established theorem. It asserts that there is a function A from inputs to pairs (a,b) of naturals computed by a polynomial-time two-stack Turing machine (TM2) on these encodings, with finite tape alphabets for all stacks, and with output encoding length bounded by a polynomial in the input encoding length, such that for every input G: b>0, a ≤ b·count(G), b·count(G) ≤ 2^(18n)·a where n is the number of vertices, and a=0 exactly when count(G)=0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SingletonLoopMatching.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SingletonLoopMatching.lean; bytes 16..3886
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


def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length false ++ true :: n.bits

def encodeRecord (r : Record) : List Bool :=
  encodeNat r.left ++ encodeNat r.right ++ encodeNat r.multiplicity

def encodeInput (G : Input) : List Bool :=
  encodeNat G.n ++ encodeNat G.records.length ++ G.records.flatMap encodeRecord

end BinaryMatching

open scoped BigOperators

namespace LoopMatching

structure LoopRecord where
  vertex : ℕ
  multiplicity : ℕ
  deriving DecidableEq

structure Input where
  ordinary : BinaryMatching.Input
  loops : List LoopRecord
  valid : ∀ e ∈ loops, e.vertex < ordinary.n
  unique : (loops.map LoopRecord.vertex).Nodup

abbrev Input.n (G : Input) : ℕ := G.ordinary.n

def loopMultiplicity (G : Input) (v : Fin G.n) : ℕ :=
  match G.loops.find? (fun r => r.vertex == v.val) with
  | none => 0
  | some r => r.multiplicity

def IsPartialMatching (n : ℕ) (M : Finset (BinaryMatching.Pair n)) : Prop :=
  ∀ v : Fin n, ∀ e ∈ M, ∀ f ∈ M,
    (BinaryMatching.completeGraph n).Incident v e →
    (BinaryMatching.completeGraph n).Incident v f → e = f

abbrev PartialMatching (n : ℕ) :=
  { M : Finset (BinaryMatching.Pair n) // IsPartialMatching n M }

noncomputable instance partialMatchingFintype (n : ℕ) : Fintype (PartialMatching n) :=
  Fintype.ofFinite _

noncomputable def loopVertices {n : ℕ} (M : PartialMatching n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v =>
    ∀ e ∈ M.val, ¬ (BinaryMatching.completeGraph n).Incident v e)

noncomputable def weight (G : Input) (M : PartialMatching G.n) : ℕ :=
  (∏ e ∈ M.val, BinaryMatching.multiplicity G.ordinary e) *
    ∏ v ∈ loopVertices M, loopMultiplicity G v

noncomputable def count (G : Input) : ℕ := ∑ M : PartialMatching G.n, weight G M


def encodeLoopRecord (r : LoopRecord) : List Bool :=
  BinaryMatching.encodeNat r.vertex ++ BinaryMatching.encodeNat r.multiplicity

def encodeInput (G : Input) : List Bool :=
  BinaryMatching.encodeInput G.ordinary ++
    BinaryMatching.encodeNat G.loops.length ++ G.loops.flatMap encodeLoopRecord

def encodeOutput (a : ℕ × ℕ) : List Bool :=
  BinaryMatching.encodeNat a.1 ++ BinaryMatching.encodeNat a.2


def FullEndpoint : Prop :=
  ∃ A : Input → ℕ × ℕ,
    ∃ machine : Turing.TM2ComputableInPolyTime encodeInput encodeOutput A,
      (∀ k, Finite (machine.tm.Γ k)) ∧
      (∃ P : Polynomial ℕ, ∀ G,
        (encodeOutput (A G)).length ≤ P.eval (encodeInput G).length) ∧
      ∀ G, 0 < (A G).2 ∧
        (A G).1 ≤ (A G).2 * count G ∧
        (A G).2 * count G ≤ 2 ^ (18 * G.n) * (A G).1 ∧
        ((A G).1 = 0 ↔ count G = 0)

end LoopMatching

namespace LoopMatching



end LoopMatching
end OAI


