-- Prove2me | Definitions.Def_VMPvsNP_SATModel
-- name    : VMPvsNP_SATModel
-- status  : Definition
-- author  : @hao jia
-- created : 2026-10-08T04:02:30.015994+00:00
-- url     : https://prove2.me/theorems/521e81bb-3c11-4ff9-a29f-270ec61791e9
-- title:
--   Binary SAT-CNF and Deterministic Multitape Machine Model
-- statement:
--   This shared model fixes binary strings as inputs and makes the SAT-CNF target language and its computational cost model explicit.
--
--   A formula is a finite list of clauses; each clause is a finite list of signed literals. A literal's natural-number index is zero-based, with external variable ID equal to index plus one. An assignment maps indices to Boolean values. Clauses use disjunction and the formula uses conjunction: the empty formula is true, an empty clause is false. SAT-CNF membership means that the entire input is exactly the encoding of a formula that has a satisfying assignment. Strings that encode no formula are outside the language.
--
--   The codec is self-delimiting Elias gamma: a natural number n is encoded as the positive gamma code of n + 1. For q clauses, use the positive gamma code of q + 1. For a clause containing r literals, use the positive gamma code of r + 1. For a literal with zero-based index v, write its negation bit followed by the positive gamma code of v + 1, its external variable ID. In particular, the variable ID is not incremented a second time. Each integer uses its usual binary digits, preceded by one fewer zero than its binary digit count. This is a disclosed concrete representation choice; equivalence with other standard SAT encodings must still be audited, not assumed from compilation alone.
--
--   A machine has arbitrary but fixed finite state, work-symbol, and tape counts. All tapes are two-way infinite and initially blank, except for the finite binary input on tape zero from position zero. Its finite transition table sees only the control state and current scanned symbols, writes only the scanned cells, and moves each head by at most one cell per step. Halting returns an explicit Boolean answer. There is no SAT oracle and no free global tape operation.
--
--   For positive integers c and k, the running-time bound is
--
--   $$p_{c,k}(x)=c\max(1,|x|)^k.$$
--
--   The halting predicate requires an actual local execution reaching the stated Boolean answer within that many transitions. This definition is reusable by the affirmative and negative SAT-CNF missions. Neither root claim is asserted or proved here.
--
--   **Formalization Note** This is a concrete foundational model, not a completed proof of encoding adequacy, NP-completeness, P = NP, or P different from NP. Its representation correspondence remains subject to statement-faithfulness review.
-- source:
--   Original shared formalization of the uniform binary SAT-CNF root targets. Background: Stephen Cook, The Complexity of Theorem-Proving Procedures, STOC 1971, pp. 151-158, https://doi.org/10.1145/800157.805047; Clay Mathematics Institute, P vs NP Problem, https://www.claymath.org/millennium/p-vs-np/ . The concrete codec and multitape interface are explicit modeling choices, not a verbatim Lean transcription of those references.

import Init.Data.Nat.ToString

namespace VMPvsNP

/-- Literal indices are zero-based; the external encoded variable ID is index + 1. -/
structure Literal where
  negated : Bool
  index : Nat
  deriving DecidableEq, Repr

abbrev CNF := List (List Literal)

/-- The standard positive Elias-gamma code for n + 1. -/
def gammaZero (n : Nat) : List Bool :=
  let bits := (Nat.toDigits 2 (n + 1)).map (fun c => c == '1')
  List.replicate (bits.length - 1) false ++ bits

def encodeLiteral (l : Literal) : List Bool :=
  l.negated :: gammaZero l.index

def encodeClause (clause : List Literal) : List Bool :=
  gammaZero clause.length ++ clause.flatMap encodeLiteral

/-- Counts are encoded plus one. Every literal carries its sign and positive ID. -/
def encodeCNF (formula : CNF) : List Bool :=
  gammaZero formula.length ++ formula.flatMap encodeClause

def formulaValue (assignment : Nat → Bool) (formula : CNF) : Bool :=
  formula.all (fun clause =>
    clause.any (fun l => assignment l.index != l.negated))

/-- No oracle is given to a machine. This predicate only specifies its target language. -/
def SATCNF (input : List Bool) : Prop :=
  ∃ formula : CNF, encodeCNF formula = input ∧
    ∃ assignment : Nat → Bool, formulaValue assignment formula = true

/-- The encoder is never empty; in particular the empty input is malformed. -/
theorem encodeCNF_ne_nil (formula : CNF) : encodeCNF formula ≠ [] := by
  intro h
  simp only [encodeCNF, gammaZero, List.append_eq_nil_iff, List.map_eq_nil_iff] at h
  exact Nat.toDigits_ne_nil h.1.2

inductive Symbol (extra : Nat) where
  | blank
  | zero
  | one
  | work (index : Fin extra)
  deriving DecidableEq, Repr

inductive Direction where
  | left
  | stay
  | right
  deriving DecidableEq, Repr

/-- A finite nonhalting control state, or an explicit Boolean halting state. -/
inductive Control (extra : Nat) where
  | running (state : Fin (extra + 1))
  | halt (answer : Bool)
  deriving DecidableEq, Repr

structure Action (states symbols tapes : Nat) where
  next : Control states
  write : Fin (tapes + 1) → Symbol symbols
  move : Fin (tapes + 1) → Direction

/-- A finite transition table: only the current finite control and scanned symbols
are arguments. Arbitrary but fixed finite state/alphabet/tape sizes are covered. -/
structure Machine where
  extraStates : Nat
  extraSymbols : Nat
  extraTapes : Nat
  transition : Fin (extraStates + 1) →
    (Fin (extraTapes + 1) → Symbol extraSymbols) →
    Action extraStates extraSymbols extraTapes

structure Configuration (M : Machine) where
  control : Control M.extraStates
  heads : Fin (M.extraTapes + 1) → Int
  tapes : Fin (M.extraTapes + 1) → Int → Symbol M.extraSymbols

/-- Input is on tape zero from position zero; all other cells/tapes are blank. -/
def initial (M : Machine) (input : List Bool) : Configuration M where
  control := .running 0
  heads := fun _ => 0
  tapes := fun tape position =>
    if tape.val = 0 ∧ 0 ≤ position then
      match input[position.toNat]? with
      | none => .blank
      | some false => .zero
      | some true => .one
    else .blank

def displacement : Direction → Int
  | .left => -1
  | .stay => 0
  | .right => 1

/-- One standard multitape step reads/writes one cell per tape, then moves each
head by at most one position. A halted configuration stays halted. -/
def step (M : Machine) (configuration : Configuration M) : Configuration M :=
  match configuration.control with
  | .halt _ => configuration
  | .running state =>
    let action := M.transition state
      (fun tape => configuration.tapes tape (configuration.heads tape))
    { control := action.next
      heads := fun tape => configuration.heads tape + displacement (action.move tape)
      tapes := fun tape position =>
        if position = configuration.heads tape then action.write tape
        else configuration.tapes tape position }

/-- The index counts actual local transitions, not formula/library operations. -/
def run (M : Machine) (input : List Bool) : Nat → Configuration M
  | 0 => initial M input
  | steps + 1 => step M (run M input steps)

def output (M : Machine) (configuration : Configuration M) : Option Bool :=
  match configuration.control with
  | .running _ => none
  | .halt answer => some answer

def HaltsWithin (M : Machine) (input : List Bool) (bound : Nat) (answer : Bool) : Prop :=
  ∃ steps : Nat, steps ≤ bound ∧ output M (run M input steps) = some answer

def polynomialBound (c k : Nat) (input : List Bool) : Nat :=
  c * (max 1 input.length) ^ k

end VMPvsNP


