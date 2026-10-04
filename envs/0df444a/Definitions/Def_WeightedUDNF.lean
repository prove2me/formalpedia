-- Prove2me | Definitions.Def_WeightedUDNF
-- name    : WeightedUDNF
-- status  : Definition
-- author  : @hao jia
-- created : 2026-10-04T10:12:15.646398+00:00
-- url     : https://prove2.me/theorems/31614ffb-52ea-459b-9f57-24f3ed6455be
-- title:
--   Weighted DNF input, semantics, and encodings
-- statement:
--   Defines finite unambiguous DNF inputs over an explicit finite variable set, their signed-literal and weighted-assignment semantics, source-validity conditions, and self-delimiting binary and unary-weight serializations. Validity requires every declared variable to occur in a literal, matching the source convention that the weighted variables are the variables of C. The binary serialization includes every list length, literal index, weight, and threshold; the unary-weight variant changes only the variable-weight payloads. Empty DNF and empty-term semantics are the standard false and true cases, respectively.
-- source:
--   Albertine Amarilli, “Weighted falsifiability for unambiguous DNFs,” List of open questions in theoretical computer science, section “Weighted falsifiability for unambiguous DNFs,” https://a3nm.net/work/research/questions/#weighted-falsifiability-for-unambiguous-dnfs.

import Mathlib.Computability.TuringMachine.Computable

namespace WeightedUDNF

abbrev Literal := Bool × Nat

/-- A finite DNF instance before imposing the source-validity conditions. -/
structure Input where
  variableCount : Nat
  terms : List (List Literal)
  weights : List Nat
  threshold : Nat
  deriving DecidableEq

/-- A unary length followed by a zero delimiter and exactly that many payload bits. -/
def unaryLengthBlock (n : Nat) : List Bool :=
  Computability.unaryEncodeNat n ++ [false]

/-- A self-delimiting block carrying the canonical binary encoding of a natural number. -/
def natBlock (n : Nat) : List Bool :=
  unaryLengthBlock (Computability.encodeNat n).length ++ Computability.encodeNat n

def encodeNatList (values : List Nat) : List Bool :=
  natBlock values.length ++ values.flatMap natBlock

def unaryNatBlock (n : Nat) : List Bool :=
  Computability.unaryEncodeNat n ++ [false]

def encodeUnaryNatList (values : List Nat) : List Bool :=
  natBlock values.length ++ values.flatMap unaryNatBlock

def encodeLiteral (literal : Literal) : List Bool :=
  literal.1 :: natBlock literal.2

def encodeTerm (term : List Literal) : List Bool :=
  natBlock term.length ++ term.flatMap encodeLiteral

def encodeTerms (terms : List (List Literal)) : List Bool :=
  natBlock terms.length ++ terms.flatMap encodeTerm

/-- Explicit binary input serialization; all list lengths and integer payloads are included. -/
def encodeInput (input : Input) : List Bool :=
  natBlock input.variableCount ++ encodeTerms input.terms ++
    encodeNatList input.weights ++ natBlock input.threshold

/-- Serialization of the same instance with only variable weights written in unary. -/
def encodeInputUnaryWeights (input : Input) : List Bool :=
  natBlock input.variableCount ++ encodeTerms input.terms ++
    encodeUnaryNatList input.weights ++ natBlock input.threshold

def readUnaryLength : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (length, tail) ← readUnaryLength rest
      some (length + 1, tail)

def readBlock (bits : List Bool) : Option (List Bool × List Bool) := do
  let (length, payload) ← readUnaryLength bits
  if length ≤ payload.length then
    some (payload.take length, payload.drop length)
  else
    none

def readNatBlock (bits : List Bool) : Option (Nat × List Bool) := do
  let (digits, rest) ← readBlock bits
  let value := Computability.decodeNat digits
  if Computability.encodeNat value = digits then
    some (value, rest)
  else
    none

def readNatListAux : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← readNatBlock bits
      let (tail, finalBits) ← readNatListAux count rest
      some (head :: tail, finalBits)

def readNatList (bits : List Bool) : Option (List Nat × List Bool) := do
  let (count, rest) ← readNatBlock bits
  readNatListAux count rest

def readUnaryNatListAux : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← readUnaryLength bits
      let (tail, finalBits) ← readUnaryNatListAux count rest
      some (head :: tail, finalBits)

def readUnaryNatList (bits : List Bool) : Option (List Nat × List Bool) := do
  let (count, rest) ← readNatBlock bits
  readUnaryNatListAux count rest

def readLiteral (bits : List Bool) : Option (Literal × List Bool) :=
  match bits with
  | positive :: rest => do
      let (index, finalBits) ← readNatBlock rest
      some ((positive, index), finalBits)
  | [] => none

def readLiteralListAux : Nat → List Bool → Option (List Literal × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← readLiteral bits
      let (tail, finalBits) ← readLiteralListAux count rest
      some (head :: tail, finalBits)

def readTerm (bits : List Bool) : Option (List Literal × List Bool) := do
  let (count, rest) ← readNatBlock bits
  readLiteralListAux count rest

def readTermsAux : Nat → List Bool → Option (List (List Literal) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (head, rest) ← readTerm bits
      let (tail, finalBits) ← readTermsAux count rest
      some (head :: tail, finalBits)

def readTerms (bits : List Bool) : Option (List (List Literal) × List Bool) := do
  let (count, rest) ← readNatBlock bits
  readTermsAux count rest

/-- Decode exactly one serialized input; trailing bits are rejected. -/
def decodeInput (bits : List Bool) : Option Input := do
  let (variableCount, rest1) ← readNatBlock bits
  let (terms, rest2) ← readTerms rest1
  let (weights, rest3) ← readNatList rest2
  let (threshold, rest4) ← readNatBlock rest3
  if rest4.isEmpty then
    some ⟨variableCount, terms, weights, threshold⟩
  else
    none

def decodeInputUnaryWeights (bits : List Bool) : Option Input := do
  let (variableCount, rest1) ← readNatBlock bits
  let (terms, rest2) ← readTerms rest1
  let (weights, rest3) ← readUnaryNatList rest2
  let (threshold, rest4) ← readNatBlock rest3
  if rest4.isEmpty then
    some ⟨variableCount, terms, weights, threshold⟩
  else
    none

def literalSatisfied (variableCount : Nat) (assignment : Fin variableCount → Bool)
    (literal : Literal) : Bool :=
  if h : literal.2 < variableCount then
    if literal.1 then assignment ⟨literal.2, h⟩ else !(assignment ⟨literal.2, h⟩)
  else
    false

def termSatisfied (variableCount : Nat) (assignment : Fin variableCount → Bool)
    (term : List Literal) : Bool :=
  term.all (literalSatisfied variableCount assignment)

def dnfSatisfied (input : Input) (assignment : Fin input.variableCount → Bool) : Bool :=
  input.terms.any (termSatisfied input.variableCount assignment)

def weightsPositive (input : Input) : Prop :=
  ∀ weight, weight ∈ input.weights → 0 < weight

def literalsInRange (input : Input) : Prop :=
  ∀ term, term ∈ input.terms →
    ∀ literal, literal ∈ term → literal.2 < input.variableCount

def variablesCovered (input : Input) : Prop :=
  ∀ index, index < input.variableCount →
    ∃ term, term ∈ input.terms ∧ ∃ literal, literal ∈ term ∧ literal.2 = index

def pairwiseUnambiguous (input : Input) : Prop :=
  input.terms.Pairwise (fun left right =>
    ¬ ∃ assignment : Fin input.variableCount → Bool,
      termSatisfied input.variableCount assignment left = true ∧
      termSatisfied input.variableCount assignment right = true)

def validInput (input : Input) : Prop :=
  input.weights.length = input.variableCount ∧
  weightsPositive input ∧
  0 < input.threshold ∧
  literalsInRange input ∧
  variablesCovered input ∧
  pairwiseUnambiguous input

def assignmentWeight (input : Input) (assignment : Fin input.variableCount → Bool) : Nat :=
  (List.range input.variableCount).foldl
    (fun total index =>
      total + if h : index < input.variableCount then
        if assignment ⟨index, h⟩ then input.weights.getD index 0 else 0
      else 0)
    0

def hasSatisfyingAssignment (input : Input) : Prop :=
  ∃ assignment : Fin input.variableCount → Bool,
    dnfSatisfied input assignment = true ∧
    input.threshold ≤ assignmentWeight input assignment

def hasFalsifyingAssignment (input : Input) : Prop :=
  ∃ assignment : Fin input.variableCount → Bool,
    dnfSatisfied input assignment = false ∧
    input.threshold ≤ assignmentWeight input assignment

noncomputable def satisfyingDecision (input : Input) : Bool := by
  classical
  exact decide (hasSatisfyingAssignment input)

noncomputable def decision (input : Input) : Bool := by
  classical
  exact decide (hasFalsifyingAssignment input)

end WeightedUDNF


