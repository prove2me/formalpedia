-- Prove2me | Definitions.Def_VertexCover
-- name    : VertexCover
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:37.539089+00:00
-- url     : https://prove2.me/theorems/d1d75f74-4dff-454d-8b28-f1477cbf96db
-- statement:
--   This block sets up 3-SAT and vertex cover as formal objects, then defines reductions and algorithms about them as bundled data. A literal is a natural-number variable name with a sign, and it evaluates under an assignment Nat → Bool to the variable's value if positive and to its negation otherwise. A clause is a vector of exactly three literals, true when at least one literal is true, and a formula is a list of clauses that is satisfiable if some assignment makes every clause true. Formulas are encoded as bit strings: a natural number is written as the list of its binary digits (Nat.bits), each digit prefixed by a true flag and the whole list ended by a false flag. A literal is its sign bit followed by its encoded name, a clause is three literals, and a clause list is a sequence of entries each marked by true and ended by false. The decoder accepts only canonical digit lists and requires that the entire input is consumed. ThreeSAT(input) holds when the input decodes to a formula that is satisfiable. An ExplicitGraph has n vertices Fin n and a duplicate-free list of edges (i,j) with i<j. A Cover is a finite vertex set containing at least one endpoint of every edge, and coverNumber is the least cardinality of such a set. The graph's bit encoding is the encoded names n, 0,…,n−1, the number of edges, and then both endpoints of each edge in order. FiniteAlphabet says every work-tape alphabet of a Turing machine (FinTM2) is finite. For m, a GapReduction is a polynomial-time Turing-computable map from bit strings to explicit graphs, with finite alphabet, such that satisfiable inputs give coverNumber < (1/2 + 1/m)·n and unsatisfiable inputs, including inputs that fail to decode, give coverNumber > (1−1/m)·n. For a real α, an Approximation is a polynomial-time computable map from graphs to lists of natural numbers (encoded with a length prefix), with finite alphabet, whose output has no repeats, uses only vertices below n, covers every edge, and has length at most α times the cover number. Finally, a ThreeSATDecision is a polynomial-time computable Boolean-valued function on bit strings, with finite alphabet, that returns true exactly on inputs satisfying ThreeSAT. These are definitions only, and no theorem relating them is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VertexCover.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VertexCover.lean; bytes 16..4841
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace UniqueGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end UniqueGames.BinaryFormula

namespace UniqueGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

def nameBits (name : Nat) : List Bool := frame name.bits

def parseName (input : List Bool) : Option (Nat × List Bool) := do
  let (digits, rest) ← parseFrame input
  let name := bitsValue digits
  if digits = name.bits then some (name, rest) else none

def parseLiteral : List Bool → Option (Literal × List Bool)
  | sign :: input => do
      let (name, rest) ← parseName input
      return (⟨name, sign⟩, rest)
  | [] => none

def parseClause (input : List Bool) : Option (Clause × List Bool) := do
  let (a, input) ← parseLiteral input
  let (b, input) ← parseLiteral input
  let (c, rest) ← parseLiteral input
  return (#v[a, b, c], rest)

def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _fuel + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end UniqueGames.BinaryEncoding

namespace VertexCover

def ThreeSAT (input : List Bool) : Prop :=
  ∃ formula, UniqueGames.BinaryEncoding.decodeFormula input = some formula ∧
    formula.Satisfiable

structure ExplicitGraph where
  n : ℕ
  edges : List (Fin n × Fin n)
  increasing : ∀ e ∈ edges, e.1 < e.2
  nodup : edges.Nodup

namespace ExplicitGraph

def Cover (G : ExplicitGraph) (S : Finset (Fin G.n)) : Prop :=
  ∀ e ∈ G.edges, e.1 ∈ S ∨ e.2 ∈ S

instance (G : ExplicitGraph) (S : Finset (Fin G.n)) : Decidable (G.Cover S) :=
  inferInstanceAs (Decidable (∀ e ∈ G.edges, e.1 ∈ S ∨ e.2 ∈ S))

noncomputable def coverNumber (G : ExplicitGraph) : ℕ :=
  Nat.find (show ∃ k : ℕ, ∃ S : Finset (Fin G.n), G.Cover S ∧ S.card = k from
    ⟨G.n, Finset.univ, by simp [Cover], by simp⟩)

def bits (G : ExplicitGraph) : List Bool :=
  let names := [G.n] ++ List.range G.n ++ [G.edges.length] ++
    G.edges.flatMap (fun e => [e.1.val, e.2.val])
  names.flatMap UniqueGames.BinaryEncoding.nameBits

end ExplicitGraph

def FiniteAlphabet (M : Turing.FinTM2) : Prop := ∀ k, Finite (M.Γ k)

structure GapReduction (m : ℕ) where
  construct : List Bool → ExplicitGraph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    ExplicitGraph.bits construct
  finiteAlphabet : FiniteAlphabet computation.tm
  completeness : ∀ input, ThreeSAT input →
    ((construct input).coverNumber : ℝ) <
      (1 / 2 + 1 / (m : ℝ)) * (construct input).n
  soundness : ∀ input, ¬ ThreeSAT input →
    (1 - 1 / (m : ℝ)) * (construct input).n <
      ((construct input).coverNumber : ℝ)

def natListBits (L : List ℕ) : List Bool :=
  (L.length :: L).flatMap UniqueGames.BinaryEncoding.nameBits

structure Approximation (α : ℝ) where
  run : ExplicitGraph → List ℕ
  computation : Turing.TM2ComputableInPolyTime ExplicitGraph.bits natListBits run
  finiteAlphabet : FiniteAlphabet computation.tm
  nodup : ∀ G, (run G).Nodup
  vertices : ∀ G, ∀ v ∈ run G, v < G.n
  covers : ∀ G, ∀ e ∈ G.edges, e.1.val ∈ run G ∨ e.2.val ∈ run G
  quality : ∀ G, ((run G).length : ℝ) ≤ α * (G.coverNumber : ℝ)

structure ThreeSATDecision where
  run : List Bool → Bool
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (fun b : Bool => [b]) run
  finiteAlphabet : FiniteAlphabet computation.tm
  correct : ∀ input, run input = true ↔ ThreeSAT input



end VertexCover
end OAI


