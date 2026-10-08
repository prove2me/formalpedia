-- Prove2me | Definitions.Def_PerfectCompleteness
-- name    : PerfectCompleteness
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.01382+00:00
-- url     : https://prove2.me/theorems/d95e8ea7-de2e-40d5-9ecf-9f04e84f6c8a
-- statement:
--   This block sets up a gap reduction from a satisfiability language of three-literal-clause formulas to labeling instances whose edge constraints are given by projection tables. Words are encoded in unary: encodeWord n is n copies of true followed by false, and encodeWords concatenates these for a list of naturals. FiniteAlphabet(M) says every work-tape alphabet Γ k of a Turing machine M is finite. A literal is a variable index with a sign, evaluating to the variable's assigned value if positive and to its negation otherwise; a clause is exactly three literals evaluated by disjunction; a formula is a list of clauses, and it is satisfiable when some assignment ℕ→Bool makes every clause true. A bit-level parser reads a variable name as a self-delimiting frame (each digit bit is preceded by true, the frame ends with false) whose little-endian digits must be the canonical binary digits of the number, then a literal as a sign bit plus a name, a clause as three literals, and a clause list as repeated true-prefixed clauses ended by false; decodeFormula succeeds only if the whole input is consumed. The language consists of bit strings decoding to a satisfiable formula. For q, a ProjectionTable is a map from Fin(2q) to Fin q in which every target has exactly two preimages; an Edge joins a left vertex and a right vertex with such a table; an Instance has numbers of left and right vertices and a nonempty list of edges. A labeling assigns each left vertex a label in Fin(2q) and each right vertex a label in Fin q, and an edge is satisfied when the table image of its left label equals its right label. The value of an instance is the maximum number of satisfied edges over all labelings divided by the number of edges, counted with multiplicity. gameBits encodes an instance as the unary words listing left and right vertex counts, q, the number of edges, and, per edge, its endpoints and the 2q table images. For rational δ, BinaryGapReduction(δ) packages a fixed alphabet size q ≥ 2 and a map from bit strings to instances over q, computable by a polynomial-time Turing machine with finite alphabets that outputs gameBits of the instance, such that every input in the language yields value exactly 1 and every input outside it yields value at most δ. The final Theorem11 namespace is empty, so no theorem is asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerfectCompleteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PerfectCompleteness.lean; bytes 16..5612
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity

def encodeWord (n : Nat) : List Bool := List.replicate n true ++ [false]

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

end UniqueGamesTheorem.Foundations.Complexity

namespace UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

open Turing

def FiniteAlphabet (M : FinTM2) : Prop := ∀ k, Finite (M.Γ k)

end UniqueGamesTheorem.Foundations.Complexity.MachineFiniteAlphabet

namespace PerfectCompleteness.BinaryFormula

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

end PerfectCompleteness.BinaryFormula

namespace PerfectCompleteness.BinaryEncoding

open PerfectCompleteness.BinaryFormula

def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bits => Nat.bit b (bitsValue bits)

def parseFrame : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: rest => do
      let (bits, trailing) ← parseFrame rest
      return (b :: bits, trailing)
  | _ => none

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
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: input => do
      let (clause, input) ← parseClause input
      let (clauses, rest) ← parseClauses fuel input
      return (clause :: clauses, rest)
  | _ + 1, [] => none

def decodeFormula (input : List Bool) : Option Formula := do
  let (clauses, rest) ← parseClauses (input.length + 1) input
  if rest = [] then some ⟨clauses⟩ else none

end PerfectCompleteness.BinaryEncoding

namespace PerfectCompleteness.BinaryLanguage

def language (input : List Bool) : Prop :=
  ∃ formula, BinaryEncoding.decodeFormula input = some formula ∧ formula.Satisfiable

end PerfectCompleteness.BinaryLanguage

namespace PerfectCompleteness

structure ProjectionTable (q : Nat) where
  images : Vector (Fin q) (2 * q)
  exactlyTwo : ∀ b : Fin q,
    ((List.finRange (2 * q)).filter (fun a => decide (images[a] = b))).length = 2

structure Edge (leftVertices rightVertices q : Nat) where
  left : Fin leftVertices
  right : Fin rightVertices
  projection : ProjectionTable q

structure Instance (q : Nat) where
  leftVertices : Nat
  rightVertices : Nat
  edges : List (Edge leftVertices rightVertices q)
  nonempty : edges ≠ []

abbrev Labeling {q : Nat} (G : Instance q) :=
  (Fin G.leftVertices → Fin (2 * q)) × (Fin G.rightVertices → Fin q)

def Edge.satisfied {l r q : Nat} (e : Edge l r q)
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) : Bool :=
  decide (e.projection.images[a e.left] = b e.right)

def countSatisfied {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) : List (Edge l r q) → Nat
  | [] => 0
  | e :: es => (if e.satisfied a b then 1 else 0) + countSatisfied a b es

end PerfectCompleteness

namespace PerfectCompleteness.Instance

def maxSatisfied {q : Nat} (G : Instance q) : Nat :=
  Finset.univ.sup (fun s : Labeling G => countSatisfied s.1 s.2 G.edges)

noncomputable def value {q : Nat} (G : Instance q) : ℝ :=
  (G.maxSatisfied : ℝ) / G.edges.length

end PerfectCompleteness.Instance

namespace PerfectCompleteness.Encoding

open UniqueGamesTheorem.Foundations.Complexity

def tableWords {q : Nat} (table : ProjectionTable q) : List Nat :=
  table.images.toList.map Fin.val

def edgeWords {l r q : Nat} (edge : Edge l r q) : List Nat :=
  [edge.left.val, edge.right.val] ++ tableWords edge.projection

def gameWords {q : Nat} (game : Instance q) : List Nat :=
  [game.leftVertices, game.rightVertices, q, game.edges.length] ++
    game.edges.flatMap edgeWords

def gameBits {q : Nat} (game : Instance q) : List Bool :=
  encodeWords (gameWords game)

end PerfectCompleteness.Encoding

namespace PerfectCompleteness

open Turing UniqueGamesTheorem.Foundations.Complexity

structure BinaryGapReduction (δ : ℚ) where
  alphabet : Nat
  alphabet_ge_two : 2 ≤ alphabet
  construct : List Bool → Instance alphabet
  computation : TM2ComputableInPolyTime (id : List Bool → List Bool)
    Encoding.gameBits construct
  finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm
  completeness : ∀ input, BinaryLanguage.language input → (construct input).value = 1
  soundness : ∀ input, ¬BinaryLanguage.language input → (construct input).value ≤ (δ : ℝ)

end PerfectCompleteness

namespace PerfectCompleteness.Theorem11



end PerfectCompleteness.Theorem11
end OAI


