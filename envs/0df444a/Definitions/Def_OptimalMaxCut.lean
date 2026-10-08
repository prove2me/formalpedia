-- Prove2me | Definitions.Def_OptimalMaxCut
-- name    : OptimalMaxCut
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:58.601423+00:00
-- url     : https://prove2.me/theorems/4728036e-175a-4f26-9834-b668a3a4531d
-- statement:
--   A literal is a natural-number variable name with a sign, evaluated under an assignment Nat → Bool as the variable or its negation; a clause has exactly three literal slots and is true when at least one is true, and a formula is a list of such clauses (repeated names and literals allowed) that is satisfiable if some assignment makes every clause true. A prefix-free binary encoding frames a bit list by prefixing each bit with a 1 and ending with a 0; a variable name is written as the framed canonical binary digits (padded alternatives are rejected), a literal as a sign bit followed by its name, a clause as three literals, and a formula as a sequence of clauses each introduced by 1 and terminated by 0, so decodeFormula returns a formula only if the whole input parses with nothing left over. binary3SAT(input) holds exactly when the input decodes to a satisfiable formula, so malformed words are rejected. alphaGW is the Goemans–Williamson ratio, defined as the infimum of 2·arccos(ρ)/(π(1−ρ)) over −1 ≤ ρ < 1. A Graph is a finite simple unweighted graph on Fin n with symmetric, loopless Boolean adjacency; cutSize counts each crossing edge once for a Boolean vertex labeling, and maxCut is the maximum over all labelings. A ScaledGraph adds a positive integer scale Q, which need not equal the edge count, and its bit encoding is the framed vertex count, the framed scale, then the full adjacency table in lexicographic order. For a real α, a GapReduction consists of rational bounds yesBound > 0 and noBound ≥ 0 with noBound < α·yesBound, together with a map from bit lists to scaled graphs computed by a fixed finite-alphabet multi-tape Turing machine (TM2) in polynomial time, such that satisfiable binary 3SAT inputs give maxCut/Q ≥ yesBound and all other inputs, including malformed ones, give maxCut/Q ≤ noBound. MainStatement is a defined proposition, not an established theorem: for every real α with alphaGW < α ≤ 1, a GapReduction α exists, i.e. a polynomial-time gap reduction from 3SAT to Max-Cut with approximation threshold α.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/OptimalMaxCut.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/OptimalMaxCut.lean; bytes 16..5434
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace MaxCutGames.BinaryFormula

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

def Literal.eval (literal : Literal) (assignment : Nat → Bool) : Bool :=
  if literal.positive then assignment literal.name else !(assignment literal.name)

abbrev Clause := Vector Literal 3

def Clause.eval (clause : Clause) (assignment : Nat → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

/-- An ordinary conjunction of three-slot clauses with sparse variable names.
Repeated names and repeated literals are permitted in every clause. -/
structure Formula where
  clauses : List Clause

def Formula.Satisfiable (F : Formula) : Prop :=
  ∃ assignment : Nat → Bool, ∀ clause ∈ F.clauses, clause.eval assignment = true

end MaxCutGames.BinaryFormula

namespace MaxCutGames.BinaryEncoding

open BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

/-- Prefix-free framing on the two-symbol input alphabet. -/
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

/-- Equality with the canonical digits rejects alternate padded encodings. -/
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

/-- Fuel bounds the number of clause iterations, not the size of any name. -/
def parseClauses : Nat → List Bool → Option (List Clause × List Bool)
  | 0, _ => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end MaxCutGames.BinaryEncoding

namespace OptimalMaxCut

open scoped BigOperators

/-- The exact Goemans–Williamson ratio, as an infimum over -1 ≤ ρ < 1. -/
noncomputable def alphaGW : ℝ :=
  sInf ((fun ρ : ℝ => 2 * Real.arccos ρ / (Real.pi * (1 - ρ))) ''
    Set.Ico (-1 : ℝ) 1)

/-- The ordinary binary 3SAT language, including rejection of malformed words. -/
def binary3SAT (input : List Bool) : Prop :=
  ∃ formula, MaxCutGames.BinaryEncoding.decodeFormula input = some formula ∧
    formula.Satisfiable

/-- A finite simple unweighted graph with its full Boolean adjacency table. -/
structure Graph where
  vertices : ℕ
  adj : Fin vertices → Fin vertices → Bool
  symmetric : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

/-- Each unordered distinct edge crossing the cut is counted exactly once. -/
def Graph.cutSize (G : Graph) (cut : Fin G.vertices → Bool) : ℕ :=
  ∑ u : Fin G.vertices, ∑ v : Fin G.vertices,
    if u < v ∧ G.adj u v = true ∧ cut u ≠ cut v then 1 else 0

/-- The maximum over all Boolean cuts of the finite vertex set. -/
def Graph.maxCut (G : Graph) : ℕ :=
  (Finset.univ.image G.cutSize).sup id

/-- The positive integer scale Q is part of the output. It need not equal the
number of graph edges. -/
structure ScaledGraph where
  graph : Graph
  scale : ℕ
  scale_pos : 0 < scale

/-- Canonical delimited binary vertex count and scale, followed by the full
adjacency table in lexicographic order. -/
def ScaledGraph.bits (G : ScaledGraph) : List Bool :=
  MaxCutGames.BinaryEncoding.nameBits G.graph.vertices ++
  MaxCutGames.BinaryEncoding.nameBits G.scale ++
  (List.finRange G.graph.vertices).flatMap (fun u =>
    (List.finRange G.graph.vertices).map (fun v => G.graph.adj u v))

/-- The rational gap bounds and the finite machine are fixed before the input.
The bounds compare the maximum cut divided by the positive output scale. -/
structure GapReduction (α : ℝ) where
  yesBound : ℚ
  noBound : ℚ
  yes_pos : 0 < yesBound
  no_nonneg : 0 ≤ noBound
  gap : (noBound : ℝ) < α * (yesBound : ℝ)
  construct : List Bool → ScaledGraph
  computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    ScaledGraph.bits construct
  finiteAlphabet : ∀ k, Finite (computation.tm.Γ k)
  completeness : ∀ input, binary3SAT input →
    (yesBound : ℝ) ≤ ((construct input).graph.maxCut : ℝ) / (construct input).scale
  soundness : ∀ input, ¬ binary3SAT input →
    ((construct input).graph.maxCut : ℝ) / (construct input).scale ≤ (noBound : ℝ)

def MainStatement : Prop :=
  ∀ α : ℝ, alphaGW < α → α ≤ 1 → Nonempty (GapReduction α)

end OptimalMaxCut



end OAI


