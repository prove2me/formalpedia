-- Prove2me | Definitions.Def_IndependentSets
-- name    : IndependentSets
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.004594+00:00
-- url     : https://prove2.me/theorems/39f5d675-2283-4eed-b028-9c7b29b57f48
-- statement:
--   This block sets up a framework for reductions from 3-SAT to a gap problem about graph independence ratios. A Literal is a variable index (a natural number) together with a sign; a Formula is a list of clauses, each a list of literals of length at most 3, and it is Satisfiable if some assignment of Booleans to variable indices makes every clause contain a literal whose variable value equals its sign. A prefix-free binary framing encodes a list of bits by writing each payload bit b as true followed by b and ending with false; natural numbers, literals (sign bit followed by the framed index), clauses (framed length followed by their literals) and whole formulas (framed clause count followed by their clauses) are then serialized into bit strings. A Graph is a nonempty finite simple undirected graph on n vertices given by a Boolean symmetric, loopless adjacency function. A set S of vertices is Independent if no two distinct members are adjacent, independenceNumber is the largest cardinality of such a set, and ThreeColorable means some coloring of vertices by three colors gives adjacent vertices different colors. A graph is serialized by the framed vertex count followed by its full row-major adjacency matrix. For a real threshold δ, a RealGraphReduction packages a map from bit strings to graphs that is computed by a multitape Turing machine in polynomial time (with finite tape alphabets and an explicit polynomial bound on the size of the serialized output) and satisfies two properties for every formula φ: completeness, meaning that if φ is satisfiable then the reduced graph is 3-colorable, and soundness, meaning that if φ is not satisfiable then the reduced graph's independence number is strictly less than δ times its number of vertices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IndependentSets.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IndependentSets.lean; bytes 16..2710
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace LargeIndependentSets

structure Literal where
  name : ℕ
  positive : Bool
  deriving DecidableEq

structure Formula where
  clauses : List (List Literal)
  width : ∀ C ∈ clauses, C.length ≤ 3

def Formula.Satisfiable (φ : Formula) : Prop :=
  ∃ assignment : ℕ → Bool, ∀ C ∈ φ.clauses,
    ∃ l ∈ C, assignment l.name = l.positive

/-- Binary framing: `true,b` for a payload bit and `false` as terminator. -/
def frame : List Bool → List Bool
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def nameBits (n : ℕ) : List Bool := frame n.bits

def literalBits (l : Literal) : List Bool := l.positive :: nameBits l.name

def clauseBits (C : List Literal) : List Bool :=
  nameBits C.length ++ C.flatMap literalBits

def formulaBits (φ : Formula) : List Bool :=
  nameBits φ.clauses.length ++ φ.clauses.flatMap clauseBits

/-- A nonempty, finite, simple, undirected, unweighted graph. -/
structure Graph where
  vertices : ℕ
  nonempty : 0 < vertices
  adj : Fin vertices → Fin vertices → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

def Graph.Independent (G : Graph) (S : Finset (Fin G.vertices)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v = false

instance (G : Graph) (S : Finset (Fin G.vertices)) : Decidable (G.Independent S) :=
  inferInstanceAs (Decidable (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.adj u v = false))

def Graph.independenceNumber (G : Graph) : ℕ :=
  ((Finset.univ : Finset (Fin G.vertices)).powerset.filter G.Independent).sup Finset.card

def Graph.ThreeColorable (G : Graph) : Prop :=
  ∃ color : Fin G.vertices → Fin 3,
    ∀ u v, G.adj u v = true → color u ≠ color v

/-- Full explicit adjacency matrix, row-major, with binary vertex count. -/
def graphBits (G : Graph) : List Bool :=
  nameBits G.vertices ++ (List.finRange G.vertices).flatMap
    (fun u => (List.finRange G.vertices).map (G.adj u))

open scoped Classical
noncomputable section

/-- Polynomial-time graph reduction with a real independence-ratio threshold. -/
structure RealGraphReduction (δ : ℝ) where
  reduce : List Bool → Graph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) graphBits reduce
  finiteAlphabets : ∀ k : computation.tm.K, Finite (computation.tm.Γ k)
  outputBound : Polynomial ℕ
  outputSize : ∀ b, (graphBits (reduce b)).length ≤ outputBound.eval b.length
  completeness : ∀ φ : Formula, φ.Satisfiable → (reduce (formulaBits φ)).ThreeColorable
  soundness : ∀ φ : Formula, ¬φ.Satisfiable →
    ((reduce (formulaBits φ)).independenceNumber : ℝ) <
      δ * (reduce (formulaBits φ)).vertices



end
end LargeIndependentSets
end OAI


