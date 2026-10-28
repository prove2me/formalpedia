-- Prove2me | Definitions.Def_OAIQ082C000
-- name    : OAIQ082C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:21:51.091196+00:00
-- url     : https://prove2.me/theorems/b16f8946-fd04-4360-ae1d-79165a057183
-- title:
--   Definitions bundle OAIQ082C000 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 718 declarations of OpenAI's Lean: 347 definitions, 29 inductive types or structures, 2 instances and 340 theorems. The definitions and types are `OAI.BinPackingCompleteness.BinaryEncoding.namesBitSize`, `OAI.BinPackingCompleteness.BinaryFormula.Clause`, `OAI.BinPackingCompleteness.BinaryFormula.Literal`, `OAI.BinPackingCompleteness.BinaryFormula.clauseNames`, `OAI.BinPackingCompleteness.BinaryHeaderMachine.Alphabet`, `OAI.BinPackingCompleteness.BinaryHeaderMachine.State`, `OAI.BinPackingCompleteness.BinaryHeaderMachine.delimiter`, `OAI.BinPackingCompleteness.BinaryHeaderMachine.tapes`, `OAI.BinPackingCompleteness.BinaryNameMachine.Alphabet`, `OAI.BinPackingCompleteness.BinaryNameMachine.Result`, `OAI.BinPackingCompleteness.BinaryNameMachine.State`, `OAI.BinPackingCompleteness.BinaryNameMachine.canonical`, `OAI.BinPackingCompleteness.BinaryNameMachine.clean`, `OAI.BinPackingCompleteness.BinaryNameMachine.exitAt`, `OAI.BinPackingCompleteness.BinaryNameMachine.finalDigit`, `OAI.BinPackingCompleteness.BinaryNameMachine.finish`, `OAI.BinPackingCompleteness.BinaryNameMachine.frame`, `OAI.BinPackingCompleteness.BinaryNameMachine.scan`, `OAI.BinPackingCompleteness.BinaryNameMachine.scanSpec`, `OAI.BinPackingCompleteness.BinaryNameMachine.steps`, `OAI.BinPackingCompleteness.BinaryPairMachine.Alphabet`, `OAI.BinPackingCompleteness.BinaryPairMachine.Label`, `OAI.BinPackingCompleteness.BinaryPairMachine.State`, `OAI.BinPackingCompleteness.BinaryPairMachine.Tape`, `OAI.BinPackingCompleteness.BinaryPairMachine.cfg`, `OAI.BinPackingCompleteness.BinaryPairMachine.copy`, `OAI.BinPackingCompleteness.BinaryPairMachine.count`, `OAI.BinPackingCompleteness.BinaryPairMachine.machine`, `OAI.BinPackingCompleteness.BinaryPairMachine.pairHaltInTime`, `OAI.BinPackingCompleteness.BinaryPairMachine.program`, `OAI.BinPackingCompleteness.BinaryPairMachine.stop`, `OAI.BinPackingCompleteness.BinaryPairMachine.tapes`, `OAI.BinPackingCompleteness.Normalization.copyVariable`, `OAI.BinPackingCompleteness.Normalization.equalityClauses`, `OAI.BinPackingCompleteness.Normalization.extendAssignment`, `OAI.BinPackingCompleteness.Normalization.freshVariable`, `OAI.BinPackingCompleteness.Normalization.gadget`, `OAI.BinPackingCompleteness.Normalization.gadgetClauses`, `OAI.BinPackingCompleteness.Normalization.mainClause`, `OAI.BinPackingCompleteness.Normalization.normalize` and 336 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Computation_Machine`, `BinPacking_Computation_MachineCanonicalOutput`, `BinPacking_Computation_MachineCloudPrefix`, `BinPacking_Computation_MachineHorner`, `BinPacking_Computation_MachineRegularInternalRow`, `BinPacking_Computation_MachineUnaryEqualityBit`, `BinPacking_Computation_MachineUnaryLessAt`, `BinPacking_Computation_PoweringMachineRow`, `BinPacking_Computation_PoweringMasterState`, `BinPacking_CookLevin_CircuitEncodingBridge`, `BinPacking_CookLevin_ConfigIndex`, `BinPacking_CookLevin_OutputOrder`, `BinPacking_CookLevin_VerifierCircuit`, `BinPacking_Expanders_ExpanderTableEnumeration`, `BinPacking_Expanders_SpectralCut`, `BinPacking_Information_GameDecoder`, `BinPacking_PCP_AlphabetRetraction`, `BinPacking_PCP_BinaryFormula`, `BinPacking_PCP_CloudRounding`, `BinPacking_PCP_GraphTransport`, `BinPacking_PCP_NormalizationEmitMachine`, `BinPacking_PCP_RawInitialPredicate`, `BinPacking_Reductions_BinaryCoordinates`, `BinPacking_Reductions_BinaryHeaderMachine`, `BinPacking_Reductions_BinaryNameCompare`, `BinPacking_Reductions_BinaryPairMachine`, `BinPacking_Reductions_BinaryTokenMachine`, `BinPacking_Reductions_MachineTransfer`, `BinPacking_Reductions_Target`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C005`, `OAIQ082C006`, `OAIQ082C007`, `OAIQ082C008`, `OAIQ082C009` and `OAIQ082C014`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

end BinPackingGames.Foundations.Target

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity

section

def encodeWords : List Nat → List Bool
  | [] => []
  | n :: ns => encodeWord n ++ encodeWords ns

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.variables, formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

theorem clausesWords_length {n : Nat} (clauses : List (Clause n)) :
    (clauses.flatMap clauseWords).length = 6 * clauses.length := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [List.flatMap_cons, List.length_append, clauseWords_length,
        List.length_cons, ih, Nat.mul_add, Nat.mul_one]
      omega

@[simp] theorem formulaWords_length (formula : Formula) :
    (formulaWords formula).length = 2 + 6 * formula.clauses.length := by
  simp only [formulaWords, List.length_append, List.length_cons, List.length_nil,
    clausesWords_length]

end

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

def parseLabel (alphabet value : Nat) : Option (Fin alphabet) :=
  if bounded : value < alphabet then some ⟨value, bounded⟩ else none

@[simp] theorem parseLabel_value {q : Nat} (label : Fin q) :
    parseLabel q label.val = some label := by simp [parseLabel, label.isLt]

@[simp] theorem parseLabels_values {q : Nat} (labels : List (Fin q)) :
    (labels.map Fin.val).mapM (parseLabel q) = some labels := by
  induction labels with
  | nil => rfl
  | cons label labels ih => simp [ih]

end BinPackingGames.Foundations.Complexity

namespace BinPackingGames.Foundations.Complexity.MachineLookupSpec

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

end BinPackingGames.Foundations.Complexity.MachineLookupSpec

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_BinaryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.variables := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

end BinPackingGames.Foundations.PCP

namespace BinPackingGames.Foundations.PCP.VerifierToCNF

open Target

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

end BinPackingGames.Foundations.PCP.VerifierToCNF

namespace BinPackingCompleteness.BinaryFormula

open BinPackingGames.Foundations

structure Literal where
  name : Nat
  positive : Bool
  deriving DecidableEq

abbrev Clause := Vector Literal 3

def clauseNames (c : Clause) : List Nat :=
  [(c)[0].name, (c)[1].name, (c)[2].name]

end BinPackingCompleteness.BinaryFormula

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_CloudRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PoweringWalks

structure PortGraph (V D : Type*) where
  rot : (V × D) ≃ (V × D)
  rot_involutive : Function.Involutive rot

abbrev Edge (V D : Type*) := V × D
abbrev Walk (V D : Type*) (t : Nat) := V × (Fin t → D)

variable {V D : Type*}

def next (G : PortGraph V D) (v : V) (d : D) : V := (G.rot (v, d)).1

@[simp] theorem rot_rot (G : PortGraph V D) (e : Edge V D) :
    G.rot (G.rot e) = e := G.rot_involutive e

def walkEnd (G : PortGraph V D) : V → List D → V
  | v, [] => v
  | v, d :: ds => walkEnd G (next G v d) ds

@[simp] theorem walkEnd_nil (G : PortGraph V D) (v : V) : walkEnd G v [] = v := rfl

@[simp] theorem walkEnd_cons (G : PortGraph V D) (v : V) (d : D) (ds : List D) :
    walkEnd G v (d :: ds) = walkEnd G (next G v d) ds := rfl

def splitHead (V D : Type*) (n : Nat) :
    Walk V D (n + 1) ≃ ((V × D) × (Fin n → D)) where
  toFun w := ((w.1, w.2 0), fun j => w.2 j.succ)
  invFun z := (z.1.1, Fin.cases z.1.2 z.2)
  left_inv w := by
    apply Prod.ext
    · rfl
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  right_inv z := rfl

def rotateHead (G : PortGraph V D) (n : Nat) : Walk V D (n + 1) ≃ Walk V D (n + 1) :=
  (splitHead V D n).trans
    ((Equiv.prodCongr G.rot (Equiv.refl (Fin n → D))).trans (splitHead V D n).symm)

@[simp] theorem rotateHead_vertex (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).1 = next G w.1 (w.2 0) := rfl

@[simp] theorem rotateHead_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    (rotateHead G n w).2 0 = (G.rot (w.1, w.2 0)).2 := rfl

@[simp] theorem rotateHead_succ (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (j : Fin n) :
    (rotateHead G n w).2 j.succ = w.2 j.succ := rfl

end BinPackingGames.Foundations.PCP.PoweringWalks

namespace BinPackingGames.Foundations.PCP

structure ConstraintGraph (V E A : Type*) where
  reverse : E ≃ E
  reverse_involutive : Function.Involutive reverse
  tail : E → V
  accepts : E → A → A → Bool
  reverse_accepts : ∀ e a b, accepts (reverse e) b a = accepts e a b

namespace ConstraintGraph

variable {V E A : Type*}

def head (G : ConstraintGraph V E A) (e : E) : V := G.tail (G.reverse e)

@[simp] theorem head_reverse (G : ConstraintGraph V E A) (e : E) :
    G.head (G.reverse e) = G.tail e := by
  simp only [head, G.reverse_involutive e]

def edgeSatisfied (G : ConstraintGraph V E A) (labeling : V → A) (e : E) : Bool :=
  G.accepts e (labeling (G.tail e)) (labeling (G.head e))

@[simp] theorem edgeSatisfied_reverse (G : ConstraintGraph V E A)
    (labeling : V → A) (e : E) :
    G.edgeSatisfied labeling (G.reverse e) = G.edgeSatisfied labeling e := by
  simpa only [edgeSatisfied, head, G.reverse_involutive e] using
    G.reverse_accepts e (labeling (G.tail e)) (labeling (G.tail (G.reverse e)))

def rejectedDarts [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) :
    Finset E := Finset.univ.filter (fun e => G.edgeSatisfied labeling e = false)

def rejectionCount [Fintype E] (G : ConstraintGraph V E A) (labeling : V → A) : Nat :=
  (G.rejectedDarts labeling).card

end ConstraintGraph

end BinPackingGames.Foundations.PCP

section

open scoped BigOperators

namespace BinPackingGames.Foundations.PCP.DegreeReplacement

open PoweringWalks

variable {V E A D : Type*}

abbrev Cloud (G : ConstraintGraph V E A) (v : V) := {e : E // G.tail e = v}

def cloudIndexEquiv (G : ConstraintGraph V E A) :
    (E × D) ≃ (Σ v : V, Cloud G v × D) where
  toFun p := ⟨G.tail p.1, (⟨p.1, rfl⟩, p.2)⟩
  invFun p := (p.2.1.val, p.2.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨⟨e, he⟩, d⟩⟩
    cases he
    rfl

def cloudRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    (Σ v : V, Cloud G v × D) ≃ (Σ v : V, Cloud G v × D) :=
  Equiv.sigmaCongrRight (fun v => (H v).rot)

theorem cloudRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (cloudRotation G H) := by
  rintro ⟨v, p⟩
  change (⟨v, (H v).rot ((H v).rot p)⟩ : Σ v : V, Cloud G v × D) = ⟨v, p⟩
  rw [(H v).rot_involutive p]

def innerRotation (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : (E × D) ≃ (E × D) :=
  ((cloudIndexEquiv G).trans (cloudRotation G H)).trans (cloudIndexEquiv G).symm

theorem innerRotation_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (innerRotation G H) := by
  intro p
  apply (cloudIndexEquiv G).injective
  simp only [innerRotation, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact cloudRotation_involutive G H _

def replacementStep (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : E × (D ⊕ Unit) → E × (D ⊕ Unit)
  | (e, Sum.inl d) =>
      let p := innerRotation G H (e, d)
      (p.1, Sum.inl p.2)
  | (e, Sum.inr u) => (G.reverse e, Sum.inr u)

theorem replacementStep_involutive (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    Function.Involutive (replacementStep G H) := by
  rintro ⟨e, p⟩
  rcases p with d | u
  · change ((innerRotation G H (innerRotation G H (e, d))).1,
        (Sum.inl ((innerRotation G H (innerRotation G H (e, d))).2) : D ⊕ Unit)) =
      (e, Sum.inl d)
    rw [innerRotation_involutive G H (e, d)]
  · change (G.reverse (G.reverse e), (Sum.inr u : D ⊕ Unit)) = (e, Sum.inr u)
    rw [G.reverse_involutive e]

def replacementPortGraph (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) : PortGraph E (D ⊕ Unit) where
  rot :=
    { toFun := replacementStep G H
      invFun := replacementStep G H
      left_inv := replacementStep_involutive G H
      right_inv := replacementStep_involutive G H }
  rot_involutive := replacementStep_involutive G H

def replacementGraph [DecidableEq A] (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) :
    ConstraintGraph E (E × (D ⊕ Unit)) A where
  reverse := (replacementPortGraph G H).rot
  reverse_involutive := (replacementPortGraph G H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl _ => decide (a = b)
    | Sum.inr _ => G.accepts p.1 a b
  reverse_accepts := by
    rintro ⟨e, p⟩ a b
    rcases p with d | u
    · change decide (b = a) = decide (a = b)
      simp [eq_comm]
    · exact G.reverse_accepts e a b

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : E → A :=
  fun e => labeling (G.tail e)

@[simp] theorem replacement_satisfied_inr [DecidableEq A]
    (G : ConstraintGraph V E A) (H : ∀ v, PortGraph (Cloud G v) D)
    (labeling : V → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied (liftLabel G labeling) (e, Sum.inr u) =
      G.edgeSatisfied labeling e := rfl

abbrev PaddedDart (_G : ConstraintGraph V E A) (dummy : V → Type*) :=
  E ⊕ (Σ v : V, dummy v)

def paddedOwner (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy → V
  | Sum.inl e => G.tail e
  | Sum.inr z => z.1

def paddedReverse (G : ConstraintGraph V E A) (dummy : V → Type*) :
    PaddedDart G dummy ≃ PaddedDart G dummy :=
  Equiv.sumCongr G.reverse (Equiv.refl (Σ v : V, dummy v))

theorem paddedReverse_involutive (G : ConstraintGraph V E A) (dummy : V → Type*) :
    Function.Involutive (paddedReverse G dummy) := by
  intro z
  cases z with
  | inl e =>
    change (Sum.inl (G.reverse (G.reverse e)) : PaddedDart G dummy) = Sum.inl e
    rw [G.reverse_involutive e]
  | inr z => rfl

def paddedGraph (G : ConstraintGraph V E A) (dummy : V → Type*) :
    ConstraintGraph V (PaddedDart G dummy) A where
  reverse := paddedReverse G dummy
  reverse_involutive := paddedReverse_involutive G dummy
  tail := paddedOwner G dummy
  accepts e a b := match e with
    | Sum.inl e => G.accepts e a b
    | Sum.inr _ => true
  reverse_accepts := by
    intro e a b
    cases e with
    | inl e => exact G.reverse_accepts e a b
    | inr z => rfl

@[simp] theorem padded_satisfied_inl (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (e : E) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inl e) =
      G.edgeSatisfied labeling e := rfl

@[simp] theorem padded_satisfied_inr (G : ConstraintGraph V E A)
    (dummy : V → Type*) (labeling : V → A) (z : Σ v : V, dummy v) :
    (paddedGraph G dummy).edgeSatisfied labeling (Sum.inr z) = true := rfl

end BinPackingGames.Foundations.PCP.DegreeReplacement

end

namespace BinPackingGames.Foundations.PCP.CloudRounding

open scoped BigOperators

section GraphRounding

open DegreeReplacement PoweringWalks

variable {V E A D : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype D]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inl (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (d : D) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inl d) =
      decide (ell e = ell (innerRotation G H (e, d)).1) := rfl

omit [Fintype V] [Fintype E] [Fintype A] [Fintype D] [DecidableEq V] [DecidableEq E] in
@[simp] theorem copied_satisfied_inr (G : ConstraintGraph V E A)
    (H : ∀ v, PortGraph (Cloud G v) D) (ell : E → A) (e : E) (u : Unit) :
    (replacementGraph G H).edgeSatisfied ell (e, Sum.inr u) =
      G.accepts e (ell e) (ell (G.reverse e)) := rfl

end GraphRounding

end BinPackingGames.Foundations.PCP.CloudRounding

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_AlphabetRetraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.QueryIncidence

abbrev Label (q : Nat) := Fin q → Bool

variable {E X : Type*} {q : Nat}

def zeroSlot (positive : 0 < q) : Fin q := ⟨0, positive⟩

def decodeRight (positive : 0 < q) (label : Label q) : Bool := label (zeroSlot positive)

def encodeRight (bit : Bool) : Label q := fun _ => bit

@[simp] theorem decode_encodeRight (positive : 0 < q) (bit : Bool) :
    decodeRight positive (encodeRight bit) = bit := rfl

@[simp] theorem card_label (q : Nat) : Fintype.card (Label q) = 2 ^ q := by
  simp [Label]

end BinPackingGames.Foundations.PCP.QueryIncidence

namespace BinPackingGames.Foundations.PCP.InitialGraph

open Target

abbrev Label := Bool × Bool × Bool
abbrev Vertex (F : Formula) := (Fin F.variables ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide
@[simp] theorem card_label : Fintype.card Label = 8 := by
  simp [Label, Fintype.card_prod]

def variableVertex (F : Formula) (v : Fin F.variables) : Vertex F := .inl (.inl v)
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Vertex F := .inl (.inr i)
def dummyVertex (F : Formula) : Vertex F := .inr ()

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

def variableValid (label : Label) : Bool :=
  decide (label.2.1 = false ∧ label.2.2 = false)

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.variables + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

end BinPackingGames.Foundations.PCP.InitialGraph

namespace BinPackingGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b c => G.accepts e (decode b) (decode c)
  reverse_accepts := fun e b c => G.reverse_accepts e (decode b) (decode c)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end BinPackingGames.Foundations.PCP.AlphabetRetraction

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_BinaryCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

end BinPackingGames.Integration.BinaryCoordinates

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialPredicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.GraphTables

open BinPackingGames.Foundations.Complexity

abbrev Label := Fin 64
abbrev RelationTable := Vector Bool 4096

def relationIndex : Label × Label ≃ Fin 4096 := finProdFinEquiv

def relationAt (table : RelationTable) (a b : Label) : Bool :=
  table[relationIndex (a, b)]

def relationOf (predicate : Label → Label → Bool) : RelationTable :=
  Vector.ofFn (fun i => predicate (relationIndex.symm i).1 (relationIndex.symm i).2)

@[simp] theorem relationAt_relationOf (predicate : Label → Label → Bool) (a b : Label) :
    relationAt (relationOf predicate) a b = predicate a b := by
  simp [relationAt, relationOf]

structure DartRow (vertices darts : Nat) where
  tail : Fin vertices
  reverseIndex : Fin darts
  relation : RelationTable

abbrev Rows (vertices darts : Nat) := Vector (DartRow vertices darts) darts

def reverseAt {n m : Nat} (rows : Rows n m) (e : Fin m) : Fin m :=
  rows[e].reverseIndex

def acceptsAt {n m : Nat} (rows : Rows n m) (e : Fin m) (a b : Label) : Bool :=
  relationAt rows[e].relation a b

def Valid {n m : Nat} (rows : Rows n m) : Prop :=
  (∀ e, reverseAt rows (reverseAt rows e) = e) ∧
  (∀ e a b, acceptsAt rows (reverseAt rows e) b a = acceptsAt rows e a b)

instance instDecidableValid {n m : Nat} (rows : Rows n m) : Decidable (Valid rows) := by
  unfold Valid
  infer_instance

structure Table where
  vertices : Nat
  darts : Nat
  rows : Rows vertices darts
  valid : Valid rows

def rowList (table : Table) : List (DartRow table.vertices table.darts) := table.rows.toList

@[simp] theorem rowList_length (table : Table) : (rowList table).length = table.darts := by
  simp [rowList]

def semantics (table : Table) : ConstraintGraph (Fin table.vertices) (Fin table.darts) Label where
  reverse :=
    { toFun := reverseAt table.rows
      invFun := reverseAt table.rows
      left_inv := table.valid.1
      right_inv := table.valid.1 }
  reverse_involutive := table.valid.1
  tail e := table.rows[e].tail
  accepts := acceptsAt table.rows
  reverse_accepts := table.valid.2

@[simp] theorem semantics_reverse (table : Table) (e : Fin table.darts) :
    (semantics table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem semantics_tail (table : Table) (e : Fin table.darts) :
    (semantics table).tail e = table.rows[e].tail := rfl

@[simp] theorem semantics_accepts (table : Table) (e : Fin table.darts) (a b : Label) :
    (semantics table).accepts e a b = relationAt table.rows[e].relation a b := rfl

def graphRows {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Rows n m :=
  Vector.ofFn (fun e => ⟨G.tail e, G.reverse e, relationOf (G.accepts e)⟩)

@[simp] theorem reverseAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    reverseAt (graphRows G) e = G.reverse e := by
  simp [reverseAt, graphRows]

@[simp] theorem acceptsAt_graphRows {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    acceptsAt (graphRows G) e a b = G.accepts e a b := by
  simp [acceptsAt, graphRows]

theorem graphRows_valid {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) :
    Valid (graphRows G) := by
  constructor
  · intro e
    simpa using G.reverse_involutive e
  · intro e a b
    simpa using G.reverse_accepts e a b

def ofGraph {n m : Nat} (G : ConstraintGraph (Fin n) (Fin m) Label) : Table :=
  ⟨n, m, graphRows G, graphRows_valid G⟩

@[simp] theorem semantics_ofGraph_reverse {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).reverse e = G.reverse e := by
  exact reverseAt_graphRows G e

@[simp] theorem semantics_ofGraph_tail {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) :
    (semantics (ofGraph G)).tail e = G.tail e := by
  change (graphRows G)[e.val].tail = G.tail e
  simp only [graphRows, Vector.getElem_ofFn]

@[simp] theorem semantics_ofGraph_accepts {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (e : Fin m) (a b : Label) :
    (semantics (ofGraph G)).accepts e a b = G.accepts e a b := by
  exact acceptsAt_graphRows G e a b

@[simp] theorem semantics_ofGraph_edgeSatisfied {n m : Nat}
    (G : ConstraintGraph (Fin n) (Fin m) Label) (labeling : Fin n → Label) (e : Fin m) :
    (semantics (ofGraph G)).edgeSatisfied labeling e = G.edgeSatisfied labeling e := by
  simp [ConstraintGraph.edgeSatisfied, ConstraintGraph.head]

def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) :
    ConstraintGraph (Fin n) (Fin m) Label where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

def bitWord (b : Bool) : Nat := if b then 1 else 0

def parseBit : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

@[simp] theorem parseBit_bitWord (b : Bool) : parseBit (bitWord b) = some b := by
  cases b <;> rfl

@[simp] theorem parseBits_bitWords (bits : List Bool) :
    (bits.map bitWord).mapM parseBit = some bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [ih]

def relationWords (relation : RelationTable) : List Nat := relation.toList.map bitWord

@[simp] theorem relationWords_length (relation : RelationTable) :
    (relationWords relation).length = 4096 := by simp [relationWords]

def parseRelation (words : List Nat) : Option RelationTable := do
  let bits ← words.mapM parseBit
  if length_ok : bits.length = 4096 then
    some ⟨bits.toArray, by simpa using length_ok⟩
  else none

@[simp] theorem parseRelation_encoded (relation : RelationTable) :
    parseRelation (relationWords relation) = some relation := by
  unfold parseRelation relationWords
  rw [parseBits_bitWords]
  simp
  exact Vector.toArray_toList

def rowWords {n m : Nat} (row : DartRow n m) : List Nat :=
  [row.tail.val, row.reverseIndex.val] ++ relationWords row.relation

def parseRow (vertices darts : Nat) : List Nat → Option (DartRow vertices darts × List Nat)
  | tail :: reverseIndex :: words => do
      let tail ← parseLabel vertices tail
      let reverseIndex ← parseLabel darts reverseIndex
      let relation ← parseRelation (words.take 4096)
      return (⟨tail, reverseIndex, relation⟩, words.drop 4096)
  | _ => none

@[simp] theorem parseRow_encoded {n m : Nat} (row : DartRow n m) (rest : List Nat) :
    parseRow n m (rowWords row ++ rest) = some (row, rest) := by
  cases row with
  | mk tail reverseIndex relation =>
      have taken := List.take_left' (l₂ := rest) (relationWords_length relation)
      have dropped := List.drop_left' (l₂ := rest) (relationWords_length relation)
      simp [rowWords, parseRow, taken, dropped]

def parseRows (vertices darts : Nat) :
    Nat → List Nat → Option (List (DartRow vertices darts) × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (row, words) ← parseRow vertices darts words
      let (rows, words) ← parseRows vertices darts count words
      return (row :: rows, words)

@[simp] theorem parseRows_encoded {n m : Nat} (rows : List (DartRow n m)) (rest : List Nat) :
    parseRows n m rows.length (rows.flatMap rowWords ++ rest) = some (rows, rest) := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [parseRows, List.append_assoc, ih]

def tableWords (table : Table) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def tableBits (table : Table) : List Bool := encodeWords (tableWords table)

def decodeTableWords : List Nat → Option Table
  | vertices :: darts :: words => do
      let (parsed, trailing) ← parseRows vertices darts darts words
      if trailing = [] then
        if length_ok : parsed.length = darts then
          let rows : Rows vertices darts := ⟨parsed.toArray, by simpa using length_ok⟩
          if valid : Valid rows then some ⟨vertices, darts, rows, valid⟩ else none
        else none
      else none
  | _ => none

@[simp] theorem decodeTableWords_encoded (table : Table) :
    decodeTableWords (tableWords table) = some table := by
  cases table with
  | mk vertices darts rows valid =>
      have parsed := parseRows_encoded rows.toList []
      simp only [Vector.length_toList, List.append_nil] at parsed
      simp [tableWords, rowList, decodeTableWords, parsed, valid, Vector.toArray_toList]

def decodeTableBits (bits : List Bool) : Option Table :=
  decodeWords bits >>= decodeTableWords

@[simp] theorem decodeTableBits_encoded (table : Table) :
    decodeTableBits (tableBits table) = some table := by
  simp [decodeTableBits, tableBits]

@[simp] theorem rowWords_length {n m : Nat} (row : DartRow n m) :
    (rowWords row).length = 4098 := by simp [rowWords]

theorem rowsWords_length {n m : Nat} (rows : List (DartRow n m)) :
    (rows.flatMap rowWords).length = 4098 * rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [ih, Nat.mul_add, Nat.add_comm]

@[simp] theorem tableWords_length (table : Table) :
    (tableWords table).length = 2 + 4098 * table.darts := by
  simp only [tableWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, rowList_length]

end BinPackingGames.Foundations.PCP.GraphTables

namespace BinPackingGames.Foundations.PCP.PortTables

open PoweringWalks

abbrev Label := GraphTables.Label

def rowIndex (vertices ports : Nat) :
    Fin vertices × Fin ports ≃ Fin (vertices * ports) := finProdFinEquiv

@[simp] theorem rowIndex_val (n d : Nat) (e : Fin n × Fin d) :
    (rowIndex n d e).val = e.2.val + d * e.1.val := rfl

structure Table (vertices ports : Nat) where
  reverseIndex : Vector (Fin (vertices * ports)) (vertices * ports)
  relations : Vector GraphTables.RelationTable (vertices * ports)
  involutive : Function.Involutive
    (fun i : Fin (vertices * ports) => reverseIndex[i])
  transpose : ∀ (i : Fin (vertices * ports)) (a b : Label),
    GraphTables.relationAt relations[reverseIndex[i]] b a =
      GraphTables.relationAt relations[i] a b

variable {n d : Nat}

def rotation (table : Table n d) (e : Fin n × Fin d) : Fin n × Fin d :=
  (rowIndex n d).symm table.reverseIndex[rowIndex n d e]

def accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) : Bool :=
  GraphTables.relationAt table.relations[rowIndex n d e] a b

@[simp] theorem rowIndex_rotation (table : Table n d) (e : Fin n × Fin d) :
    rowIndex n d (rotation table e) = table.reverseIndex[rowIndex n d e] := by
  exact (rowIndex n d).apply_symm_apply _

theorem rotation_involutive (table : Table n d) : Function.Involutive (rotation table) := by
  intro e
  simp only [rotation, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex n d).symm (table.involutive (rowIndex n d e))).trans
    ((rowIndex n d).symm_apply_apply e)

theorem accepts_rotation (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    accepts table (rotation table e) b a = accepts table e a b := by
  simpa only [accepts, rowIndex_rotation] using table.transpose (rowIndex n d e) a b

def portGraph (table : Table n d) : PortGraph (Fin n) (Fin d) where
  rot :=
    { toFun := rotation table
      invFun := rotation table
      left_inv := rotation_involutive table
      right_inv := rotation_involutive table }
  rot_involutive := rotation_involutive table

@[simp] theorem portGraph_rot (table : Table n d) (e : Fin n × Fin d) :
    (portGraph table).rot e = rotation table e := rfl

def baseGraph (table : Table n d) : ConstraintGraph (Fin n) (Fin n × Fin d) Label where
  reverse := (portGraph table).rot
  reverse_involutive := rotation_involutive table
  tail := Prod.fst
  accepts := accepts table
  reverse_accepts := accepts_rotation table

@[simp] theorem baseGraph_reverse (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).reverse e = rotation table e := rfl

@[simp] theorem baseGraph_tail (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).tail e = e.1 := rfl

@[simp] theorem baseGraph_head (table : Table n d) (e : Fin n × Fin d) :
    (baseGraph table).head e = (rotation table e).1 := rfl

@[simp] theorem baseGraph_accepts (table : Table n d) (e : Fin n × Fin d) (a b : Label) :
    (baseGraph table).accepts e a b = accepts table e a b := rfl

end BinPackingGames.Foundations.PCP.PortTables

namespace BinPackingGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := by fin_cases i; rfl

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def binaryOrder (n : Nat) : (Fin n → Bool) ≃ Fin (2 ^ n) where
  toFun bits := (BinPackingGames.Integration.BinaryCoordinates.pack bits).toFin
  invFun index := BinPackingGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index)
  left_inv bits := BinPackingGames.Integration.BinaryCoordinates.unpack_pack bits
  right_inv index := by
    change (BinPackingGames.Integration.BinaryCoordinates.pack
      (BinPackingGames.Integration.BinaryCoordinates.unpack (BitVec.ofFin index))).toFin = index
    rw [BinPackingGames.Integration.BinaryCoordinates.pack_unpack]

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.variables + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.variables + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

end BinPackingGames.Foundations.PCP.RawInitialTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

end BinPackingGames.Foundations.Complexity.Runtime

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_MachineTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Reduction.MachineTransfer

open Turing

abbrev alphabet (α β : Type) : Bool → Type
  | false => α
  | true => β

variable {α β : Type} [Fintype α] [Fintype β]

def loop (f : α → β) (fallback : β) :
    TM2.Stmt (alphabet α β) Unit (Option β) :=
  .pop false (fun _ head => head.map f)
    (.branch Option.isSome
      (.push true (fun state => state.getD fallback) (.goto fun _ => ()))
      .halt)

def machine (f : α → β) (fallback : β) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := alphabet α β
  Λ := Unit
  main := ()
  σ := Option β
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype α)
  m _ := loop f fallback

def tapeStacks (input : List α) (output : List β) :
    (side : Bool) → List (alphabet α β side)
  | false => input
  | true => output

def running (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) : (machine f fallback).Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (f : α → β) (fallback : β) (output : List β) : (machine f fallback).Cfg :=
  ⟨none, none, tapeStacks (α := α) [] output⟩

omit [Fintype α] [Fintype β] in
theorem update_input (input replacement : List α) (output : List β) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> rfl

omit [Fintype α] [Fintype β] in
theorem update_output (input : List α) (output replacement : List β) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> rfl

theorem step_empty (f : α → β) (fallback : β) (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback [] output state) =
      some (halted f fallback output) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (α := α) [] output)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input]
  rfl

theorem step_cons (f : α → β) (fallback : β) (head : α) (input : List α)
    (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback (head :: input) output state) =
      some (running f fallback input (f head :: output) (some (f head))) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input, update_output]
  rfl

def next (f : α → β) (fallback : β) (configuration : Option (machine f fallback).Cfg) :
    Option (machine f fallback).Cfg := configuration.bind (machine f fallback).step

theorem transfer_steps (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) :
    (next f fallback)^[input.length + 1] (some (running f fallback input output state)) =
      some (halted f fallback (input.reverse.map f ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using step_empty f fallback output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (next f fallback)^[input.length + 1]
      ((machine f fallback).step (running f fallback (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem initList_eq (f : α → β) (fallback : β) (input : List α) :
    initList (machine f fallback) input = running f fallback input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (f : α → β) (fallback : β) (output : List β) :
    haltList (machine f fallback) output = halted f fallback output := by
  unfold haltList halted
  congr 1
  funext side
  cases side <;> rfl

theorem transfer_init_steps (f : α → β) (fallback : β) (input : List α) :
    (next f fallback)^[input.length + 1] (some (initList (machine f fallback) input)) =
      some (haltList (machine f fallback) (input.reverse.map f)) := by
  erw [initList_eq (α := α) (β := β) f fallback input,
    haltList_eq (α := α) (β := β) f fallback (input.reverse.map f)]
  simpa only [List.append_nil] using transfer_steps f fallback input [] none

def outputsInTime (f : α → β) (fallback : β) (input : List α) :
    TM2OutputsInTime (machine f fallback) input (some (input.reverse.map f))
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := transfer_init_steps f fallback input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (f : α → β) (fallback : β) (input : List α) :
    (outputsInTime f fallback input).steps = input.length + 1 := rfl

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def exitAt (dst : K) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def loopAt (src dst : K) (f : Γ src → Γ dst) (fallback : Γ dst)
    (loopLabel : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun state head => (state.1, head.map f))
    (.branch (fun state => state.2.isSome)
      (.push dst (fun state => state.2.getD fallback) (.goto fun _ => loopLabel))
      (exitAt dst exit))

def tapesAt (src dst : K) (base : (k : K) → List (Γ k))
    (input : List (Γ src)) (output : List (Γ dst)) : (k : K) → List (Γ k) :=
  Function.update (Function.update base src input) dst output

@[simp] theorem tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output src = input := by
  simp [tapesAt, distinct]

@[simp] theorem tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output dst = output := by
  simp [tapesAt]

@[simp] theorem tapesAt_self (src dst : K) (base : (k : K) → List (Γ k)) :
    tapesAt src dst base (base src) (base dst) = base := by
  simp [tapesAt]

theorem update_tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input replacement : List (Γ src))
    (output : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) src replacement =
      tapesAt src dst base replacement output := by
  funext k
  by_cases hs : k = src
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = dst
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src))
    (output replacement : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) dst replacement =
      tapesAt src dst base input replacement := by
  funext k
  by_cases hd : k = dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

def nextAt (dst : K) (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (configuration : Option (TM2.Cfg Γ Λ (σ × Option (Γ dst)))) :
    Option (TM2.Cfg Γ Λ (σ × Option (Γ dst))) :=
  configuration.bind (TM2.step program)

theorem stepAt_empty (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program ⟨some loopLabel, (ambient, register), tapesAt src dst base [] output⟩ =
      some ⟨exit, (ambient, none), tapesAt src dst base [] output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base [] output)) = _
  rw [atLoop]
  cases exit <;>
    simp [loopAt, exitAt, TM2.stepAux, tapesAt_src, distinct, update_tapesAt_src]

theorem stepAt_cons (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (head : Γ src) (input : List (Γ src))
    (output : List (Γ dst)) (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some (f head)),
        tapesAt src dst base input (f head :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base (head :: input) output)) = _
  rw [atLoop]
  simp [loopAt, TM2.stepAux, tapesAt_src, tapesAt_dst, distinct,
    update_tapesAt_src, update_tapesAt_dst]

theorem transferAt_steps (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register), tapesAt src dst base input output⟩) =
      some ⟨exit, (ambient, none), tapesAt src dst base [] (input.reverse.map f ++ output)⟩ := by
  induction input generalizing output register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, nextAt,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using stepAt_empty src dst distinct f fallback loopLabel exit program atLoop base output
        ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (nextAt dst program)^[input.length + 1]
      (TM2.step program
        ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩) = _
    rw [stepAt_cons src dst distinct f fallback loopLabel exit program atLoop, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem transferAt_fromTapes (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[(base src).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩ := by
  simpa only [tapesAt_self] using
    transferAt_steps src dst distinct f fallback loopLabel exit program atLoop base
      (base src) (base dst) ambient register

end BinPackingGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineUnaryLessAt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

end BinPackingGames.Foundations.Complexity.MachineEmbedding

namespace BinPackingGames.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

end BinPackingGames.Foundations.Complexity.MachineStackSwap

namespace BinPackingGames.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

end BinPackingGames.Foundations.Complexity.MachineComposition

namespace BinPackingGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (slots 0) left) (slots 1) right) (slots 2) savedLeft) (slots 3) savedRight

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

@[simp] theorem transferLeft_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementLeft : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 2) (slots 0)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementLeft =
      tapes slots base replacementLeft right replacementSaved savedRight := by
  simp [Reduction.MachineTransfer.tapesAt]

@[simp] theorem transferRight_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementRight : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 3) (slots 1)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementRight =
      tapes slots base left replacementRight savedLeft replacementSaved := by
  simp [Reduction.MachineTransfer.tapesAt]

end BinPackingGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCanonicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineFiniteSequence

open Turing MachineComposition

variable {Command : Type} (LocalLabel : Command → Type)

def Label : List Command → Type
  | [] => Empty
  | command :: commands => LocalLabel command ⊕ Label commands

end BinPackingGames.Foundations.Complexity.MachineFiniteSequence

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineUnaryEqualityBit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineCompare

open Turing
open BinPackingGames.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end BinPackingGames.Foundations.Complexity.MachineCompare

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMasterState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

end BinPackingGames.Foundations.Complexity.MachineUnaryCounter

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Information_GameDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad

section

open scoped BigOperators
open Finset

abbrev Cube (I : Type*) := I → Bool

def bitSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

def cubeXor {I : Type*} (x y : Cube I) : Cube I := fun i => x i ^^ y i

def walsh {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) : ℝ :=
  ∏ i, bitSign (s i && x i)

@[simp] theorem walsh_sq {I : Type*} [Fintype I] [DecidableEq I] (s x : Cube I) :
    walsh s x ^ 2 = 1 := by
  simp [walsh, ← Finset.prod_pow]

open scoped BigOperators
open Finset

end

section

open scoped BigOperators
open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

def cubeFlip (f : Cube I) : Cube I := fun i => !(f i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem cubeFlip_cubeFlip (f : Cube I) : cubeFlip (cubeFlip f) = f := by
  funext i
  simp [cubeFlip]

end

open scoped BigOperators
open Finset

end BinPackingGames.Foundations.Hastad

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.SpectralReturn

open PoweringWalks
open scoped BigOperators

def averagingOperator {V D : Type*} [Fintype D] (G : PortGraph V D)
    (f : V → ℝ) (v : V) : ℝ := Finset.univ.expect (fun d => f (G.rot (v, d)).1)

end BinPackingGames.Foundations.PCP.SpectralReturn

namespace BinPackingGames.Foundations.PCP.CayleySpectral

open scoped BigOperators
open Finset
open BinPackingGames.Foundations.Hastad
open PoweringWalks

variable {I D : Type*}

def zeroFrequency : Cube I := fun _ => false

theorem cubeXor_cancel_right (x y : Cube I) :
    cubeXor (cubeXor x y) y = x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXor, hx, hy]

@[simp] theorem cubeXor_zeroFrequency (x : Cube I) :
    cubeXor x zeroFrequency = x := by
  funext i
  cases hx : x i <;> simp [cubeXor, zeroFrequency, hx]

def rotate (g : D → Cube I) (p : Cube I × D) : Cube I × D :=
  (cubeXor p.1 (g p.2), p.2)

theorem rotate_involutive (g : D → Cube I) : Function.Involutive (rotate g) := by
  rintro ⟨x, d⟩
  change (cubeXor (cubeXor x (g d)) (g d), d) = (x, d)
  rw [cubeXor_cancel_right]

def cayleyGraph (g : D → Cube I) : PortGraph (Cube I) D where
  rot :=
    { toFun := rotate g
      invFun := rotate g
      left_inv := rotate_involutive g
      right_inv := rotate_involutive g }
  rot_involutive := rotate_involutive g

@[simp] theorem cayleyGraph_rot (g : D → Cube I) (x : Cube I) (d : D) :
    (cayleyGraph g).rot (x, d) = (cubeXor x (g d), d) := rfl

variable [Fintype I] [DecidableEq I] [Fintype D]

def cayleyAverage (g : D → Cube I) (f : Cube I → ℝ) (x : Cube I) : ℝ :=
  𝔼 d, f ((cayleyGraph g).rot (x, d)).1

omit [Fintype I] [DecidableEq I] in
@[simp] theorem averagingOperator_cayleyGraph (g : D → Cube I) (f : Cube I → ℝ) :
    SpectralReturn.averagingOperator (cayleyGraph g) f = cayleyAverage g f := rfl

end BinPackingGames.Foundations.PCP.CayleySpectral

namespace BinPackingGames.Foundations.PCP.ZigzagGraphs

open PoweringWalks

variable {V D E : Type*}

def involutionEquiv {A : Type*} (f : A → A) (hf : Function.Involutive f) : A ≃ A where
  toFun := f
  invFun := f
  left_inv := hf
  right_inv := hf

theorem palindrome_involutive {A : Type*} (B P : A ≃ A)
    (hB : Function.Involutive B) (hP : Function.Involutive P) :
    Function.Involutive (B.trans (P.trans B)) := by
  intro x
  change B (P (B (B (P (B x))))) = x
  rw [hB, hP, hB]

def squareFirst (G : PortGraph V D) (s : V × (D × D)) : V × (D × D) :=
  let step := G.rot (s.1, s.2.1)
  (step.1, (step.2, s.2.2))

theorem squareFirst_involutive (G : PortGraph V D) : Function.Involutive (squareFirst G) := by
  rintro ⟨v, d₁, d₂⟩
  change ((G.rot (G.rot (v, d₁))).1, ((G.rot (G.rot (v, d₁))).2, d₂)) =
    (v, (d₁, d₂))
  rw [G.rot_involutive]

def squareSwap (s : V × (D × D)) : V × (D × D) := (s.1, (s.2.2, s.2.1))

theorem squareSwap_involutive : Function.Involutive (squareSwap (V := V) (D := D)) := by
  rintro ⟨v, d₁, d₂⟩
  rfl

def square (G : PortGraph V D) : PortGraph V (D × D) := by
  let B := involutionEquiv (squareFirst G) (squareFirst_involutive G)
  let P := involutionEquiv (squareSwap (V := V) (D := D)) squareSwap_involutive
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (squareFirst_involutive G) squareSwap_involutive }

@[simp] theorem square_rot_apply (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    (square G).rot (v, (d₁, d₂)) =
      let first := G.rot (v, d₁)
      let second := G.rot (first.1, d₂)
      (second.1, (second.2, first.2)) := rfl

@[simp] theorem square_next (G : PortGraph V D) (v : V) (d₁ d₂ : D) :
    next (square G) v (d₁, d₂) = next G (next G v d₁) d₂ := rfl

def cloudFirst (H : PortGraph D E) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) :=
  let step := H.rot (s.1.2, s.2.1)
  ((s.1.1, step.1), (step.2, s.2.2))

theorem cloudFirst_involutive (H : PortGraph D E) :
    Function.Involutive (cloudFirst (V := V) H) := by
  rintro ⟨⟨v, d⟩, ⟨e₁, e₂⟩⟩
  change ((v, (H.rot (H.rot (d, e₁))).1), ((H.rot (H.rot (d, e₁))).2, e₂)) =
    ((v, d), (e₁, e₂))
  rw [H.rot_involutive]

def crossCloud (G : PortGraph V D) (s : (V × D) × (E × E)) :
    (V × D) × (E × E) := (G.rot s.1, (s.2.2, s.2.1))

theorem crossCloud_involutive (G : PortGraph V D) :
    Function.Involutive (crossCloud (E := E) G) := by
  rintro ⟨x, e₁, e₂⟩
  change (G.rot (G.rot x), (e₁, e₂)) = (x, (e₁, e₂))
  rw [G.rot_involutive]

def zigzag (G : PortGraph V D) (H : PortGraph D E) : PortGraph (V × D) (E × E) := by
  let B := involutionEquiv (cloudFirst (V := V) H) (cloudFirst_involutive H)
  let P := involutionEquiv (crossCloud (E := E) G) (crossCloud_involutive G)
  exact
    { rot := B.trans (P.trans B)
      rot_involutive := palindrome_involutive B P
        (cloudFirst_involutive H) (crossCloud_involutive G) }

@[simp] theorem zigzag_rot_apply (G : PortGraph V D) (H : PortGraph D E)
    (v : V) (d : D) (e₁ e₂ : E) :
    (zigzag G H).rot ((v, d), (e₁, e₂)) =
      let first := H.rot (d, e₁)
      let middle := G.rot (v, first.1)
      let last := H.rot (middle.2, e₂)
      ((middle.1, last.1), (last.2, first.2)) := rfl

end BinPackingGames.Foundations.PCP.ZigzagGraphs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_GraphTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.GraphTransport

open PoweringWalks SpectralReturn

variable {V W D E : Type*}

def reindex (G : PortGraph V D) (vertices : V ≃ W) (ports : D ≃ E) :
    PortGraph W E where
  rot := (Equiv.prodCongr vertices ports).symm.trans
    (G.rot.trans (Equiv.prodCongr vertices ports))
  rot_involutive := by
    intro x
    change (Equiv.prodCongr vertices ports)
        (G.rot ((Equiv.prodCongr vertices ports).symm
          ((Equiv.prodCongr vertices ports)
            (G.rot ((Equiv.prodCongr vertices ports).symm x))))) = x
    rw [Equiv.symm_apply_apply, G.rot_involutive, Equiv.apply_symm_apply]

@[simp] theorem reindex_rot (G : PortGraph V D) (vertices : V ≃ W)
    (ports : D ≃ E) (v : V) (d : D) :
    (reindex G vertices ports).rot (vertices v, ports d) =
      (vertices (G.rot (v, d)).1, ports (G.rot (v, d)).2) := by
  simp [reindex, Equiv.trans_apply, Prod.map]

end BinPackingGames.Foundations.PCP.GraphTransport

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Expanders_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.CayleySampling

open scoped BigOperators
open Finset
open BinPackingGames.Foundations.Hastad

variable {V D : Type*}

abbrev FalseFiber (χ : V → Bool) := {x : V // χ x = false}

def falseRepresentative (χ : V → Bool) (flip : V → V)
    (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) : FalseFiber χ :=
  if h : χ x = false then ⟨x, h⟩
  else ⟨flip x, by cases hx : χ x <;> simp_all⟩

def booleanSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    V ≃ Bool × FalseFiber χ where
  toFun x := (χ x, falseRepresentative χ flip hχ x)
  invFun p := if p.1 then flip p.2.val else p.2.val
  left_inv x := by
    cases hx : χ x <;> simp [falseRepresentative, hx]
    exact hflip x
  right_inv p := by
    rcases p with ⟨b, x⟩
    apply Prod.ext
    · cases b <;> simp [hχ, x.property]
    · cases b <;> apply Subtype.ext <;>
        simp [falseRepresentative, hχ, x.property]
      exact hflip x.val

@[simp] theorem booleanSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (x : V) :
    (booleanSplitEquiv χ flip hflip hχ x).1 = χ x := rfl

def sampleSplitEquiv (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) :
    (D → V) ≃ (D → Bool) × (D → FalseFiber χ) :=
  (Equiv.piCongrRight fun _ : D => booleanSplitEquiv χ flip hflip hχ).trans
    (Equiv.arrowProdEquivProdArrow D (fun _ => Bool) (fun _ => FalseFiber χ))

@[simp] theorem sampleSplitEquiv_fst (χ : V → Bool) (flip : V → V)
    (hflip : Function.Involutive flip) (hχ : ∀ x, χ (flip x) = !(χ x)) (g : D → V) :
    (sampleSplitEquiv χ flip hflip hχ g).1 = fun d => χ (g d) := rfl

end BinPackingGames.Foundations.PCP.CayleySampling

namespace BinPackingGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

def graph {v d : Nat} (table : Table v d) : PortGraph (Fin v) (Fin d) where
  rot := ZigzagGraphs.involutionEquiv (lookup table) (lookup_involutive table)
  rot_involutive := lookup_involutive table

@[simp] theorem graph_rot {v d : Nat} (table : Table v d) (x : Fin v × Fin d) :
    (graph table).rot x = lookup table x := rfl

def ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) : Table v d where
  rows := Vector.ofFn (fun i => rowIndex v d (G.rot ((rowIndex v d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
    exact (congrArg (rowIndex v d) (G.rot_involutive ((rowIndex v d).symm i))).trans
      ((rowIndex v d).apply_symm_apply i)

@[simp] theorem lookup_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d))
    (x : Fin v × Fin d) : lookup (ofGraph G) x = G.rot x := by
  simp only [lookup, reverseIndex, ofGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

end BinPackingGames.Foundations.PCP.ExpanderTables

namespace BinPackingGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

abbrev degree (d : Nat) : Nat := d * d
abbrev cloudSize (d : Nat) : Nat := degree d * degree d

structure Control (d : Nat) where
  firstH : Fin (cloudSize d) × Fin d
  lastInput : Fin d
  firstG : Fin (degree d)
  secondG : Fin (degree d)
  lastH : Fin (cloudSize d) × Fin d
  deriving DecidableEq, Fintype

def squarePorts {d : Nat} (s : Control d) : Fin (degree d) × Fin (degree d) :=
  (rowIndex (degree d) (degree d)).symm s.firstH.1

def receiveFirst {d : Nat} (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with firstG := returnedPort }

def receiveSecond {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with
    secondG := returnedPort
    lastH := lookup H
      (rowIndex (degree d) (degree d) (returnedPort,s.firstG),s.lastInput) }

def firstOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).1
def secondOffset {d : Nat} (s : Control d) : Fin (degree d) := (squarePorts s).2

@[simp] theorem firstOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    firstOffset (receiveFirst s r) = firstOffset s := rfl

@[simp] theorem secondOffset_receiveFirst {d : Nat} (s : Control d) (r : Fin (degree d)) :
    secondOffset (receiveFirst s r) = secondOffset s := rfl

@[simp] theorem receiveFirst_port {d : Nat} (s : Control d) (r : Fin (degree d)) :
    (receiveFirst s r).firstG = r := rfl

@[simp] theorem receiveSecond_port {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (r : Fin (degree d)) : (receiveSecond H s r).secondG = r := rfl

end BinPackingGames.Foundations.PCP.ExpanderRowControl

namespace BinPackingGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open BinPackingGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

@[simp] theorem decode_rotationWords (table : Table v d) :
    decodeWords (encodeWords (rotationWords table)) = some (rotationWords table) :=
  Complexity.decodeWords_encodeWords _

end BinPackingGames.Foundations.PCP.ExpanderTableWords

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryAddAt

open Turing
open Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (destination : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun state => (state.1, none)) (exitAt destination exit)

def loop (source destination : K) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push destination (fun _ => true) (.goto fun _ => loopLabel))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false) (finish destination exit))
        (finish destination exit)))

def unaryTapes (source destination : K) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) : K → List Bool :=
  tapesAt source destination base (encodeWord a ++ sourceSuffix)
    (encodeWord b ++ destinationSuffix)

@[simp] theorem unaryTapes_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix source =
      encodeWord a ++ sourceSuffix := by
  simp [unaryTapes, distinct]

@[simp] theorem unaryTapes_destination (source destination : K)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool) :
    unaryTapes source destination base a b sourceSuffix destinationSuffix destination =
      encodeWord b ++ destinationSuffix := by
  simp [unaryTapes]

theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  funext k
  by_cases hd : k = destination
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

theorem stepAux_true (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (true :: input) output) =
      ⟨some loopLabel, (ambient, some true),
        tapesAt source destination base input (true :: output)⟩ := by
  simp [loop, TM2.stepAux, distinct, update_source, update_destination]

theorem stepAux_false (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool)
    (input output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (tapesAt source destination base (false :: input) output) =
      ⟨exit, (ambient, none), tapesAt source destination base (false :: input) output⟩ := by
  cases exit <;> simp [loop, finish, exitAt, TM2.stepAux, distinct, update_source]

theorem stepAux_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (a b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix) =
      ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append] using
    stepAux_true source destination distinct loopLabel exit base
      (encodeWord a ++ sourceSuffix) (encodeWord b ++ destinationSuffix) ambient register

theorem stepAux_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ) (base : K → List Bool) (b : Nat)
    (sourceSuffix destinationSuffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (loop source destination loopLabel exit) (ambient, register)
      (unaryTapes source destination base 0 b sourceSuffix destinationSuffix) =
      ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  simpa only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append] using
    stepAux_false source destination distinct loopLabel exit base sourceSuffix
      (encodeWord b ++ destinationSuffix) ambient register

theorem step_succ (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩ =
      some ⟨some loopLabel, (ambient, some true),
        unaryTapes source destination base a (b + 1) sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_succ source destination distinct]

theorem step_zero (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some loopLabel, (ambient, register),
      unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 b sourceSuffix destinationSuffix⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (unaryTapes source destination base 0 b sourceSuffix destinationSuffix)) = _
  rw [atLoop, stepAux_zero source destination distinct]

theorem addTrace (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base a b sourceSuffix destinationSuffix⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  induction a generalizing b register with
  | zero =>
    simpa only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      step_zero source destination distinct loopLabel exit program atLoop
        base b sourceSuffix destinationSuffix ambient register
  | succ a ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[a + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        unaryTapes source destination base (a + 1) b sourceSuffix destinationSuffix⟩) = _
    rw [step_succ source destination distinct loopLabel exit program atLoop]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1) (some true)

theorem addFromTapes (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[a + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩ := by
  have hbase : unaryTapes source destination base a b sourceSuffix destinationSuffix =
      base := by
    simp only [unaryTapes, ← sourceInput, ← destinationInput, tapesAt_self]
  have h := addTrace source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix ambient register
  rw [hbase] at h
  exact h

def addInTime (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        unaryTapes source destination base 0 (a + b) sourceSuffix destinationSuffix⟩)
      (a + 1) where
  steps := a + 1
  evals_in_steps := addFromTapes source destination distinct loopLabel exit program atLoop
    base a b sourceSuffix destinationSuffix sourceInput destinationInput ambient register
  steps_le_m := Nat.le_refl _

@[simp] theorem addInTime_steps (source destination : K) (distinct : source ≠ destination)
    (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLoop : program loopLabel = loop source destination loopLabel exit)
    (base : K → List Bool) (a b : Nat) (sourceSuffix destinationSuffix : List Bool)
    (sourceInput : base source = encodeWord a ++ sourceSuffix)
    (destinationInput : base destination = encodeWord b ++ destinationSuffix)
    (ambient : σ) (register : Option Bool) :
    (addInTime source destination distinct loopLabel exit program atLoop base a b
      sourceSuffix destinationSuffix sourceInput destinationInput ambient register).steps =
      a + 1 := rfl

end BinPackingGames.Foundations.Complexity.MachineUnaryAddAt

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (product : ℕ) : K → List Bool :=
  Function.update base (slots 2) (encodeWord product ++ base (slots 2))

@[simp] theorem resultTapes_output (slots : Fin 5 ↪ K) (base : K → List Bool) (p : ℕ) :
    resultTapes slots base p (slots 2) = encodeWord p ++ base (slots 2) := by
  simp [resultTapes]

end BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

namespace BinPackingGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

def multiplySlots (slots : Fin 6 ↪ K) : Fin 5 ↪ K :=
  (Fin.succAboveEmb (2 : Fin 6)).trans slots

@[simp] theorem multiplySlots_zero (slots : Fin 6 ↪ K) : multiplySlots slots 0 = slots 0 := rfl
@[simp] theorem multiplySlots_one (slots : Fin 6 ↪ K) : multiplySlots slots 1 = slots 1 := rfl
@[simp] theorem multiplySlots_two (slots : Fin 6 ↪ K) : multiplySlots slots 2 = slots 3 := rfl
@[simp] theorem multiplySlots_three (slots : Fin 6 ↪ K) : multiplySlots slots 3 = slots 4 := rfl
@[simp] theorem multiplySlots_four (slots : Fin 6 ↪ K) : multiplySlots slots 4 = slots 5 := rfl

variable [DecidableEq K]

def resultTapes (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) : K → List Bool :=
  Function.update base (slots 3) (encodeWord value ++ base (slots 3))

@[simp] theorem resultTapes_output (slots : Fin 6 ↪ K) (base : K → List Bool) (value : ℕ) :
    resultTapes slots base value (slots 3) = encodeWord value ++ base (slots 3) := by
  simp [resultTapes]

end BinPackingGames.Foundations.Complexity.MachineRadixStep

namespace BinPackingGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

abbrev Layout (width : Nat) := Fin 6 ⊕ Fin width

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

def accumulator (flip : Bool) : Fin 6 := if flip then 2 else 1

@[simp] theorem accumulator_ne (flip : Bool) : accumulator flip ≠ accumulator (!flip) := by
  cases flip <;> decide

def radixLayout (flip : Bool) (i : Fin width) : Fin 6 ↪ Layout width where
  toFun
    | 0 => .inl 0
    | 1 => .inl (accumulator flip)
    | 2 => .inr i
    | 3 => .inl (accumulator (!flip))
    | 4 => .inl 4
    | 5 => .inl 5
  inj' := by
    intro a b h
    cases flip <;> fin_cases a <;> fin_cases b <;> simp [accumulator] at h ⊢

def radixSlots (slots : Layout width ↪ K) (i : Fin width) : Fin 6 ↪ K :=
  (radixLayout (parity i.val) i).trans slots

@[simp] theorem radixSlots_base (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 0 = slots (.inl 0) := rfl
@[simp] theorem radixSlots_acc (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 1 = slots (.inl (accumulator (parity i.val))) := rfl
@[simp] theorem radixSlots_digit (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 2 = slots (.inr i) := rfl
@[simp] theorem radixSlots_out (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 3 = slots (.inl (accumulator (parity (i.val + 1)))) := rfl
@[simp] theorem radixSlots_counter (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 4 = slots (.inl 4) := rfl
@[simp] theorem radixSlots_scratch (slots : Layout width ↪ K) (i : Fin width) :
    radixSlots slots i 5 = slots (.inl 5) := rfl

variable [DecidableEq K]

def resultTapes (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) : K → List Bool :=
  Function.update base (slots (.inl 3)) (encodeWord acc ++ base (slots (.inl 3)))

open scoped BigOperators

@[simp] theorem resultTapes_output (slots : Layout width ↪ K) (base : K → List Bool) (acc : Nat) :
    resultTapes slots base acc (slots (.inl 3)) = encodeWord acc ++ base (slots (.inl 3)) := by
  simp [resultTapes]

end BinPackingGames.Foundations.Complexity.MachineHorner

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularInternalRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularInternalRow

open Turing MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]

abbrev CoreTape := Fin 27

end BinPackingGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ConfigIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.StackEncoding

variable {Γ : Type*}

abbrev Cells (Γ : Type*) (S : Nat) := Fin S → Option Γ

def encode (S : Nat) (xs : List Γ) : Cells Γ S := fun i => xs[i.val]?

@[simp] theorem encode_apply (S : Nat) (xs : List Γ) (i : Fin S) :
    encode S xs i = xs[i.val]? := rfl

@[simp] theorem encode_nil (S : Nat) : encode S ([] : List Γ) = fun _ => none := by
  funext i
  simp [encode]

end BinPackingGames.Foundations.Complexity.CookLevin.StackEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin

open Target

inductive Gate where
  | const (value : Bool)
  | not (input : Nat)
  | and (left right : Nat)
  | or (left right : Nat)
  deriving DecidableEq

def Gate.Bounded (g : Gate) (bound : Nat) : Prop :=
  match g with
  | .const _ => True
  | .not x => x < bound
  | .and x y | .or x y => x < bound ∧ y < bound

def Gate.eval (g : Gate) (wires : Nat → Bool) : Bool :=
  match g with
  | .const b => b
  | .not x => !(wires x)
  | .and x y => wires x && wires y
  | .or x y => wires x || wires y

theorem Gate.bounded_mono (g : Gate) {a b : Nat} (hab : a ≤ b)
    (h : g.Bounded a) : g.Bounded b := by
  cases g with
  | const _ => trivial
  | not _ => exact Nat.lt_of_lt_of_le h hab
  | and _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩
  | or _ _ => exact ⟨Nat.lt_of_lt_of_le h.1 hab, Nat.lt_of_lt_of_le h.2 hab⟩

def Ordered (start : Nat) (gates : List Gate) : Prop :=
  ∀ i (hi : i < gates.length), gates[i].Bounded (start + i)

def Consistent (start : Nat) (gates : List Gate) (wires : Nat → Bool) : Prop :=
  ∀ i (hi : i < gates.length), wires (start + i) = gates[i].eval wires

@[simp] theorem ordered_nil (start : Nat) : Ordered start [] := by
  intro i hi
  simp at hi

theorem ordered_cons (start : Nat) (g : Gate) (gs : List Gate) :
    Ordered start (g :: gs) ↔ g.Bounded start ∧ Ordered (start + 1) gs := by
  unfold Ordered
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      change g.Bounded (start + 0) at h0
      simpa only [Nat.add_zero] using h0
    · intro i hi
      have ht := h (i + 1) (by simpa using hi)
      change gs[i].Bounded (start + (i + 1)) at ht
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
  · rintro ⟨hg, hgs⟩ i hi
    cases i with
    | zero => simpa using hg
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hgs i (by simpa using hi)

@[simp] theorem consistent_nil (start : Nat) (A : Nat → Bool) :
    Consistent start [] A := by
  intro i hi
  simp at hi

def run (start : Nat) : List Gate → (Nat → Bool) → (Nat → Bool)
  | [], A => A
  | g :: gs, A => run (start + 1) gs (Function.update A start (g.eval A))

theorem run_eq_of_lt (start : Nat) (gs : List Gate) (A : Nat → Bool)
    (j : Nat) (hj : j < start) : run start gs A j = A j := by
  induction gs generalizing start A with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih (start + 1) _ (by omega)]
    exact Function.update_of_ne (by omega) _ _

@[simp] theorem run_singleton (start : Nat) (g : Gate) (A : Nat → Bool) :
    run start [g] A = Function.update A start (g.eval A) := rfl

@[simp] theorem run_singleton_here (start : Nat) (g : Gate) (A : Nat → Bool) :
    run start [g] A start = g.eval A := by simp

theorem Ordered.append {start : Nat} {gs hs : List Gate}
    (hg : Ordered start gs) (hh : Ordered (start + gs.length) hs) :
    Ordered start (gs ++ hs) := by
  induction gs generalizing start with
  | nil => simpa using hh
  | cons g gs ih =>
    rcases (ordered_cons start g gs).mp hg with ⟨h0, ht⟩
    apply (ordered_cons start g (gs ++ hs)).mpr
    refine ⟨h0, ih ht ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

structure Circuit where
  inputs : Nat
  gates : List Gate
  ordered : Ordered inputs gates
  output : Fin (inputs + gates.length)

abbrev Circuit.wires (C : Circuit) : Nat := C.inputs + C.gates.length

def inputEnv {n : Nat} (input : Fin n → Bool) : Nat → Bool :=
  fun j => if h : j < n then input ⟨j, h⟩ else false

def Circuit.evalWires (C : Circuit) (input : Fin C.inputs → Bool) : Nat → Bool :=
  run C.inputs C.gates (inputEnv input)

def Circuit.eval (C : Circuit) (input : Fin C.inputs → Bool) : Bool :=
  C.evalWires input C.output.val

def unitClause {n : Nat} (wire : Fin n) (positive : Bool) : Clause n :=
  #v[⟨wire, positive⟩, ⟨wire, positive⟩, ⟨wire, positive⟩]

def gateClauses {n : Nat} (output : Fin n) : (g : Gate) → g.Bounded n → List (Clause n)
  | .const b, _ => [unitClause output b, unitClause output b, unitClause output b]
  | .not x, h =>
    let v : Fin n := ⟨x, h⟩
    [#v[⟨output, true⟩, ⟨v, true⟩, ⟨v, true⟩],
     #v[⟨output, false⟩, ⟨v, false⟩, ⟨v, false⟩],
     #v[⟨output, true⟩, ⟨v, true⟩, ⟨v, true⟩]]
  | .and x y, h =>
    let vx : Fin n := ⟨x, h.1⟩
    let vy : Fin n := ⟨y, h.2⟩
    [#v[⟨output, false⟩, ⟨vx, true⟩, ⟨vx, true⟩],
     #v[⟨output, false⟩, ⟨vy, true⟩, ⟨vy, true⟩],
     #v[⟨output, true⟩, ⟨vx, false⟩, ⟨vy, false⟩]]
  | .or x y, h =>
    let vx : Fin n := ⟨x, h.1⟩
    let vy : Fin n := ⟨y, h.2⟩
    [#v[⟨output, true⟩, ⟨vx, false⟩, ⟨vx, false⟩],
     #v[⟨output, true⟩, ⟨vy, false⟩, ⟨vy, false⟩],
     #v[⟨output, false⟩, ⟨vx, true⟩, ⟨vy, true⟩]]

@[simp] theorem gateClauses_length {n : Nat} (output : Fin n)
    (g : Gate) (h : g.Bounded n) : (gateClauses output g h).length = 3 := by
  cases g <;> rfl

def Circuit.gateAt (C : Circuit) (i : Fin C.gates.length) : Gate := C.gates[i.val]

def Circuit.gateOutput (C : Circuit) (i : Fin C.gates.length) : Fin C.wires :=
  ⟨C.inputs + i.val, by have hi := i.isLt; simp only [Circuit.wires]; omega⟩

theorem Circuit.gateBounded (C : Circuit) (i : Fin C.gates.length) :
    (C.gateAt i).Bounded C.wires :=
  Gate.bounded_mono _ (by have hi := i.isLt; simp only [Circuit.wires]; omega)
    (C.ordered i.val i.isLt)

def Circuit.gateBlock (C : Circuit) (i : Fin C.gates.length) : List (Clause C.wires) :=
  gateClauses (C.gateOutput i) (C.gateAt i) (C.gateBounded i)

def Circuit.toFormula (C : Circuit) : Formula where
  «variables» := C.wires
  clauses := (List.finRange C.gates.length).flatMap C.gateBlock ++ [unitClause C.output true]

@[simp] theorem Circuit.toFormula_variables (C : Circuit) :
    C.toFormula.variables = C.inputs + C.gates.length := rfl

@[simp] theorem Circuit.toFormula_clause_count (C : Circuit) :
    C.toFormula.clauses.length = 3 * C.gates.length + 1 := by
  have h : ∀ is : List (Fin C.gates.length),
      (is.flatMap C.gateBlock).length = 3 * is.length := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.flatMap_cons, List.length_append, Circuit.gateBlock,
        gateClauses_length, List.length_cons] at *
      omega
  simp [Circuit.toFormula, h]

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

open Turing
open StackEncoding

inductive Expr (ι : Type*) where
  | input (index : ι)
  | const (value : Bool)
  | not (arg : Expr ι)
  | and (left right : Expr ι)
  | or (left right : Expr ι)

namespace Expr

variable {ι : Type*}

def eval (input : ι → Bool) : Expr ι → Bool
  | .input i => input i
  | .const b => b
  | .not e => !(eval input e)
  | .and e f => eval input e && eval input f
  | .or e f => eval input e || eval input f

def rename {κ : Type*} (f : ι → κ) : Expr ι → Expr κ
  | .input i => .input (f i)
  | .const b => .const b
  | .not e => .not (e.rename f)
  | .and e g => .and (e.rename f) (g.rename f)
  | .or e g => .or (e.rename f) (g.rename f)

@[simp] theorem eval_rename {κ : Type*} (f : ι → κ) (e : Expr ι) (input : κ → Bool) :
    (e.rename f).eval input = e.eval (fun i => input (f i)) := by
  induction e <;> simp_all [rename, eval]

def size : Expr ι → Nat
  | .input _ | .const _ => 1
  | .not e => e.size + 1
  | .and e f | .or e f => e.size + f.size + 1

theorem size_pos (e : Expr ι) : 0 < e.size := by
  cases e <;> simp [size]

@[simp] theorem size_rename {κ : Type*} (f : ι → κ) (e : Expr ι) :
    (e.rename f).size = e.size := by
  induction e <;> simp_all [rename, size]

def root (start : Nat) (e : Expr ι) : Nat := start + e.size - 1

theorem root_lt (start : Nat) (e : Expr ι) : e.root start < start + e.size := by
  have := e.size_pos
  unfold root
  omega

@[simp] theorem root_not (start : Nat) (e : Expr ι) :
    (Expr.not e).root start = start + e.size := by
  simp only [root, size]
  omega

@[simp] theorem root_and (start : Nat) (e f : Expr ι) :
    (Expr.and e f).root start = start + (e.size + f.size) := by
  simp only [root, size]
  omega

@[simp] theorem root_or (start : Nat) (e f : Expr ι) :
    (Expr.or e f).root start = start + (e.size + f.size) := by
  simp only [root, size]
  omega

def gates (wire : ι → Nat) (start : Nat) : Expr ι → List Gate
  | .input i => [.or (wire i) (wire i)]
  | .const b => [.const b]
  | .not e => e.gates wire start ++ [.not (e.root start)]
  | .and e f => e.gates wire start ++ f.gates wire (start + e.size) ++
      [.and (e.root start) (f.root (start + e.size))]
  | .or e f => e.gates wire start ++ f.gates wire (start + e.size) ++
      [.or (e.root start) (f.root (start + e.size))]

@[simp] theorem gates_length (e : Expr ι) (wire : ι → Nat) (start : Nat) :
    (e.gates wire start).length = e.size := by
  induction e generalizing start <;> simp_all [gates, size, Nat.add_assoc]

theorem ordered_singleton (start : Nat) (g : Gate) (h : g.Bounded start) :
    Ordered start [g] := by
  exact (ordered_cons start g []).mpr ⟨h, ordered_nil _⟩

theorem gates_ordered (e : Expr ι) (wire : ι → Nat) (start : Nat)
    (hw : ∀ i, wire i < start) : Ordered start (e.gates wire start) := by
  induction e generalizing start with
  | input i => exact ordered_singleton start _ ⟨hw i, hw i⟩
  | const b => exact ordered_singleton start _ trivial
  | not e ih =>
    apply (ih start hw).append
    simpa only [gates_length] using
      ordered_singleton (start + e.size) (.not (e.root start)) (e.root_lt start)
  | and e f ihe ihf =>
    have hf := ihf (start + e.size) (fun i => lt_of_lt_of_le (hw i) (by omega))
    have hp : Ordered start (e.gates wire start ++ f.gates wire (start + e.size)) :=
      (ihe start hw).append (by simpa only [gates_length] using hf)
    apply hp.append
    simp only [List.length_append, gates_length]
    apply ordered_singleton
    exact ⟨lt_of_lt_of_le (e.root_lt start) (by omega), by
      simpa only [Nat.add_assoc] using f.root_lt (start + e.size)⟩
  | or e f ihe ihf =>
    have hf := ihf (start + e.size) (fun i => lt_of_lt_of_le (hw i) (by omega))
    have hp : Ordered start (e.gates wire start ++ f.gates wire (start + e.size)) :=
      (ihe start hw).append (by simpa only [gates_length] using hf)
    apply hp.append
    simp only [List.length_append, gates_length]
    apply ordered_singleton
    exact ⟨lt_of_lt_of_le (e.root_lt start) (by omega), by
      simpa only [Nat.add_assoc] using f.root_lt (start + e.size)⟩

def mux (condition yes no : Expr ι) : Expr ι :=
  .or (.and condition yes) (.and (.not condition) no)

@[simp] theorem eval_mux (input : ι → Bool) (c x y : Expr ι) :
    (mux c x y).eval input = if c.eval input then x.eval input else y.eval input := by
  cases hc : c.eval input <;> simp [mux, eval, hc]

def disjoin : List (Expr ι) → Expr ι
  | [] => .const false
  | e :: rest => .or e (disjoin rest)

end Expr

noncomputable def table {ι A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Expr ι) (b : B) : Expr ι :=
  Expr.disjoin (Finset.univ.toList.map (fun a => .and (x a) (.const (decide (f a = b)))))

noncomputable def table₂ {ι A B C : Type*} [Fintype A] [Fintype B] [DecidableEq C]
    (f : A → B → C) (x : A → Expr ι) (y : B → Expr ι) (c : C) : Expr ι :=
  table (fun p : A × B => f p.1 p.2) (fun p => .and (x p.1) (y p.2)) c

section Encoding

variable {K : Type} {Γ : K → Type} {Λ σ : Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [DecidableEq Λ]

abbrev InputBit (Γ : K → Type) (σ : Type) (S : Nat) :=
  σ ⊕ (Σ k, Fin S × Option (Γ k))

abbrev ConfigBit (Γ : K → Type) (Λ σ : Type) (S : Nat) :=
  Option Λ ⊕ InputBit Γ σ S

def inputEncoding (S : Nat) (v : σ) (tapes : ∀ k, List (Γ k)) : InputBit Γ σ S → Bool
  | .inl w => decide (v = w)
  | .inr ⟨k, i, a⟩ => decide (encode S (tapes k) i = a)

def configEncoding (S : Nat) (cfg : TM2.Cfg Γ Λ σ) : ConfigBit Γ Λ σ S → Bool
  | .inl label => decide (cfg.l = label)
  | .inr i => inputEncoding S cfg.var cfg.stk i

end Encoding

end BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.ConfigIndex

open StatementCircuit

variable {K : Type} (Γ : K → Type) (Λ σ : Type)

abbrev SymbolBit := Σ k, Option (Γ k)

structure Indexing where
  labelCount : Nat
  stateCount : Nat
  symbolCount : Nat
  labels : Option Λ ≃ Fin labelCount
  states : σ ≃ Fin stateCount
  symbols : SymbolBit Γ ≃ Fin symbolCount

variable {Γ Λ σ}

def Indexing.width (indexing : Indexing Γ Λ σ) (S : Nat) : Nat :=
  indexing.labelCount + indexing.stateCount + S * indexing.symbolCount

def cellReorder (S : Nat) : (Σ k, Fin S × Option (Γ k)) ≃ (Fin S × SymbolBit Γ) where
  toFun cell := (cell.2.1, ⟨cell.1, cell.2.2⟩)
  invFun cell := ⟨cell.2.1, cell.1, cell.2.2⟩
  left_inv cell := by rcases cell with ⟨k, i, a⟩; rfl
  right_inv cell := by rcases cell with ⟨i, k, a⟩; rfl

def Indexing.configIndexEquiv (indexing : Indexing Γ Λ σ) (S : Nat) :
    ConfigBit Γ Λ σ S ≃ Fin (indexing.width S) :=
  (Equiv.sumCongr indexing.labels
    (Equiv.sumCongr indexing.states
      ((cellReorder S).trans
        ((Equiv.prodCongr (Equiv.refl (Fin S)) indexing.symbols).trans finProdFinEquiv)))).trans
    ((Equiv.sumAssoc (Fin indexing.labelCount) (Fin indexing.stateCount)
      (Fin (S * indexing.symbolCount))).symm.trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin (S * indexing.symbolCount)))).trans
        finSumFinEquiv))

@[simp] theorem Indexing.configIndex_label (indexing : Indexing Γ Λ σ)
    (S : Nat) (label : Option Λ) :
    (indexing.configIndexEquiv S (.inl label)).val = (indexing.labels label).val := by
  rfl

@[simp] theorem Indexing.configIndex_state (indexing : Indexing Γ Λ σ)
    (S : Nat) (state : σ) :
    (indexing.configIndexEquiv S (.inr (.inl state))).val =
      indexing.labelCount + (indexing.states state).val := by
  rfl

@[simp] theorem Indexing.configIndex_cell (indexing : Indexing Γ Λ σ)
    (S : Nat) (k : K) (i : Fin S) (symbol : Option (Γ k)) :
    (indexing.configIndexEquiv S (.inr (.inr ⟨k, i, symbol⟩))).val =
      indexing.labelCount + indexing.stateCount + i.val * indexing.symbolCount +
        (indexing.symbols ⟨k, symbol⟩).val := by
  change indexing.labelCount + indexing.stateCount +
    ((indexing.symbols ⟨k, symbol⟩).val + indexing.symbolCount * i.val) = _
  rw [Nat.mul_comm indexing.symbolCount i.val]
  omega

noncomputable def ofMachine (machine : Turing.FinTM2)
    [∀ k, Fintype (machine.Γ k)] : Indexing machine.Γ machine.Λ machine.σ := by
  letI := machine.kFin
  letI := machine.ΛFin
  letI := machine.σFin
  exact {
    labelCount := Fintype.card (Option machine.Λ)
    stateCount := Fintype.card machine.σ
    symbolCount := Fintype.card (SymbolBit machine.Γ)
    labels := Fintype.equivFin (Option machine.Λ)
    states := Fintype.equivFin machine.σ
    symbols := Fintype.equivFin (SymbolBit machine.Γ) }

end BinPackingGames.Foundations.Complexity.CookLevin.ConfigIndex

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_CircuitEncodingBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

open Turing
open BinPackingGames.Foundations.Hastad
open BinPackingGames.Reduction

structure Record where
  tag : Fin 5
  output : Nat
  first : Nat
  second : Nat
  deriving DecidableEq

def Record.words (r : Record) : List Nat :=
  [r.tag.val, r.output, r.first, r.second]

def Record.bits (r : Record) : List Bool := encodeWords r.words

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitProducerModel

namespace BinPackingGames.Foundations.Complexity.CookLevin

open CircuitProducerModel

def gateRecord (output : Nat) : Gate → Record
  | .const false => ⟨0, output, 0, 0⟩
  | .const true => ⟨1, output, 0, 0⟩
  | .not a => ⟨2, output, a, 0⟩
  | .and a b => ⟨3, output, a, b⟩
  | .or a b => ⟨4, output, a, b⟩

def gateRecords (start : Nat) : List Gate → List Record
  | [] => []
  | g :: gs => gateRecord start g :: gateRecords (start + 1) gs

def Circuit.records (C : Circuit) : List Record := gateRecords C.inputs C.gates

def recordsWords (rs : List Record) : List Nat := rs.flatMap Record.words
def recordsBits (rs : List Record) : List Bool := encodeWords (recordsWords rs)

def circuitWords (C : Circuit) : List Nat :=
  [C.wires, C.gates.length, C.output.val] ++ recordsWords C.records

@[simp] theorem gateRecords_length (start : Nat) (gs : List Gate) :
    (gateRecords start gs).length = gs.length := by
  induction gs generalizing start with
  | nil => rfl
  | cons g gs ih => simp [gateRecords, ih]

@[simp] theorem Circuit.records_length (C : Circuit) : C.records.length = C.gates.length :=
  gateRecords_length C.inputs C.gates

@[simp] theorem recordsWords_cons (r : Record) (rs : List Record) :
    recordsWords (r :: rs) = r.words ++ recordsWords rs := rfl

@[simp] theorem recordsBits_cons (r : Record) (rs : List Record) :
    recordsBits (r :: rs) = r.bits ++ recordsBits rs := by
  simp [recordsBits, Record.bits]

@[simp] theorem recordsWords_length (rs : List Record) :
    (recordsWords rs).length = 4 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      rw [recordsWords_cons, List.length_append, ih]
      simp only [Record.words, List.length_cons, List.length_nil]
      omega

@[simp] theorem circuitWords_length (C : Circuit) :
    (circuitWords C).length = 3 + 4 * C.gates.length := by
  simp [circuitWords]
  omega

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

inductive Token where
  | const (value : Bool)
  | not | and | or
  | input (wire : Nat)
  deriving DecidableEq

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixModel

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_OutputOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

inductive Position where
  | current
  | zero
  | succ (p : Position)
  | pred (p : Position)
  deriving DecidableEq

def Position.eval (cursor : Nat) : Position → Nat
  | .current => cursor
  | .zero => 0
  | .succ p => p.eval cursor + 1
  | .pred p => p.eval cursor - 1

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

open StatementCircuit

namespace Batch

variable {ι : Type*}

def cost (es : List (Expr ι)) : Nat := (es.map Expr.size).sum

def gates (wire : ι → Nat) (start : Nat) : List (Expr ι) → List Gate
  | [] => []
  | e :: es => e.gates wire start ++ gates wire (start + e.size) es

def roots (start : Nat) : List (Expr ι) → List Nat
  | [] => []
  | e :: es => e.root start :: roots (start + e.size) es

@[simp] theorem cost_nil : cost ([] : List (Expr ι)) = 0 := rfl

@[simp] theorem cost_cons (e : Expr ι) (es : List (Expr ι)) :
    cost (e :: es) = e.size + cost es := by simp [cost]

@[simp] theorem gates_length (wire : ι → Nat) (start : Nat) (es : List (Expr ι)) :
    (gates wire start es).length = cost es := by
  induction es generalizing start with
  | nil => rfl
  | cons e es ih => simp [gates, ih]

@[simp] theorem roots_length (start : Nat) (es : List (Expr ι)) :
    (roots start es).length = es.length := by
  induction es generalizing start <;> simp [roots, *]

theorem gates_ordered (wire : ι → Nat) (start : Nat) (es : List (Expr ι))
    (hw : ∀ i, wire i < start) : Ordered start (gates wire start es) := by
  induction es generalizing start with
  | nil => exact ordered_nil start
  | cons e es ih =>
    apply (e.gates_ordered wire start hw).append
    simpa only [Expr.gates_length] using
      ih (start + e.size) (fun i => lt_of_lt_of_le (hw i) (by omega))

theorem roots_bounds (start : Nat) (es : List (Expr ι)) (r : Nat)
    (hr : r ∈ roots start es) : start ≤ r ∧ r < start + cost es := by
  induction es generalizing start with
  | nil => simp [roots] at hr
  | cons e es ih =>
    simp only [roots, List.mem_cons] at hr
    rcases hr with rfl | hr
    · have hp := e.size_pos
      have hu := e.root_lt start
      simp only [cost_cons]
      constructor
      · unfold Expr.root; omega
      · omega
    · have ht := ih (start + e.size) hr
      simp only [cost_cons]
      omega

def rootAt (start : Nat) (es : List (Expr ι)) (i : Fin es.length) : Nat :=
  (roots start es)[i.val]'(by simpa only [roots_length] using i.isLt)

theorem rootAt_lt (start : Nat) (es : List (Expr ι)) (i : Fin es.length) :
    rootAt start es i < start + cost es := by
  have hr : rootAt start es i ∈ roots start es :=
    List.mem_of_getElem (rfl :
      (roots start es)[i.val]'(by simpa only [roots_length] using i.isLt) = rootAt start es i)
  exact (roots_bounds start es _ hr).2

end Batch

structure Fragment (inputs : Nat) where
  gates : List Gate
  ordered : Ordered inputs gates

namespace Fragment

variable {inputs : Nat}

def empty (inputs : Nat) : Fragment inputs := ⟨[], ordered_nil inputs⟩

def evalWires (f : Fragment inputs) (input : Fin inputs → Bool) : Nat → Bool :=
  run inputs f.gates (inputEnv input)

theorem evalWires_input (f : Fragment inputs) (input : Fin inputs → Bool)
    (j : Fin inputs) : f.evalWires input j.val = input j := by
  rw [evalWires, run_eq_of_lt _ _ _ _ j.isLt]
  simp [inputEnv, j.isLt]

def append (f : Fragment inputs) (gs : List Gate)
    (hg : Ordered (inputs + f.gates.length) gs) : Fragment inputs :=
  ⟨f.gates ++ gs, f.ordered.append hg⟩

def toCircuit (f : Fragment inputs) (output : Fin (inputs + f.gates.length)) : Circuit :=
  ⟨inputs, f.gates, f.ordered, output⟩

@[simp] theorem toCircuit_eval (f : Fragment inputs)
    (output : Fin (inputs + f.gates.length)) (input : Fin inputs → Bool) :
    (f.toCircuit output).eval input = f.evalWires input output.val := rfl

end Fragment

structure Frame (inputs width : Nat) where
  fragment : Fragment inputs
  wires : Fin width → Fin (inputs + fragment.gates.length)

namespace Frame

variable {inputs width oldWidth newWidth : Nat}

def eval (f : Frame inputs width) (input : Fin inputs → Bool) : Fin width → Bool :=
  fun i => f.fragment.evalWires input (f.wires i).val

def initial (wire : Fin width → Fin inputs) : Frame inputs width where
  fragment := Fragment.empty inputs
  wires := wire

@[simp] theorem initial_eval (wire : Fin width → Fin inputs) (input : Fin inputs → Bool)
    (i : Fin width) : (initial wire).eval input i = input (wire i) :=
  (Fragment.empty inputs).evalWires_input input (wire i)

def step (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth)) :
    Frame inputs newWidth where
  fragment := f.fragment.append
    (Batch.gates (fun i => (f.wires i).val) (inputs + f.fragment.gates.length) (List.ofFn es))
    (Batch.gates_ordered _ _ _ (fun i => (f.wires i).isLt))
  wires := fun i => ⟨Batch.rootAt (inputs + f.fragment.gates.length) (List.ofFn es)
      ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩, by
    have h := Batch.rootAt_lt (inputs + f.fragment.gates.length) (List.ofFn es)
      ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
    simpa only [Fragment.append, List.length_append, Batch.gates_length, Nat.add_assoc] using h⟩

@[simp] theorem step_gate_count (f : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    (f.step es).fragment.gates.length =
      f.fragment.gates.length + Batch.cost (List.ofFn es) := by
  simp only [step, Fragment.append, List.length_append, Batch.gates_length]

def toCircuit (f : Frame inputs width) (output : Fin width) : Circuit :=
  f.fragment.toCircuit (f.wires output)

@[simp] theorem toCircuit_eval (f : Frame inputs width) (output : Fin width)
    (input : Fin inputs → Bool) : (f.toCircuit output).eval input = f.eval input output := rfl

end Frame

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitBatch

namespace BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

open StatementCircuit CircuitBatch PostfixModel

variable {ι : Type*}

def exprTokens (wire : ι → Nat) : Expr ι → List Token
  | .input i => [.input (wire i)]
  | .const b => [.const b]
  | .not e => exprTokens wire e ++ [.not]
  | .and e f => exprTokens wire e ++ exprTokens wire f ++ [.and]
  | .or e f => exprTokens wire e ++ exprTokens wire f ++ [.or]

def forestTokens (wire : ι → Nat) (es : List (Expr ι)) : List Token :=
  es.flatMap (exprTokens wire)

@[simp] theorem exprTokens_length (wire : ι → Nat) (e : Expr ι) :
    (exprTokens wire e).length = e.size := by
  induction e <;> simp_all [exprTokens, Expr.size, Nat.add_assoc]

@[simp] theorem exprTokens_rename {κ : Type*} (f : ι → κ) (wire : κ → Nat) (e : Expr ι) :
    exprTokens wire (e.rename f) = exprTokens (fun i => wire (f i)) e := by
  induction e <;> simp_all [Expr.rename, exprTokens]

@[simp] theorem forestTokens_nil (wire : ι → Nat) :
    forestTokens wire ([] : List (Expr ι)) = [] := rfl

@[simp] theorem forestTokens_cons (wire : ι → Nat) (e : Expr ι) (es : List (Expr ι)) :
    forestTokens wire (e :: es) = exprTokens wire e ++ forestTokens wire es := rfl

@[simp] theorem forestTokens_length (wire : ι → Nat) (es : List (Expr ι)) :
    (forestTokens wire es).length = Batch.cost es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [forestTokens_cons, List.length_append, exprTokens_length,
      ih, Batch.cost_cons]

end BinPackingGames.Foundations.Complexity.CookLevin.PostfixAlignment

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

open Turing StatementCircuit

variable {K : Type} (Γ : K → Type) (σ : Type)

inductive Term where
  | state (v : σ)
  | cell (k : K) (position : Position) (symbol : Option (Γ k))
  | const (value : Bool)
  | not (arg : Term)
  | and (left right : Term)
  | or (left right : Term)
  | atZero (position : Position) (yes no : Term)
  | within (position : Position) (yes no : Term)

variable {Γ σ} [∀ k, DecidableEq (Γ k)]

def Term.instantiate (S cursor : Nat) : Term Γ σ → Expr (InputBit Γ σ S)
  | .state v => .input (.inl v)
  | .cell k p a => if h : p.eval cursor < S then .input (.inr ⟨k, ⟨p.eval cursor, h⟩, a⟩)
      else .const (decide ((none : Option (Γ k)) = a))
  | .const b => .const b
  | .not e => .not (e.instantiate S cursor)
  | .and e f => .and (e.instantiate S cursor) (f.instantiate S cursor)
  | .or e f => .or (e.instantiate S cursor) (f.instantiate S cursor)
  | .atZero p yes no => if p.eval cursor = 0 then yes.instantiate S cursor
      else no.instantiate S cursor
  | .within p yes no => if p.eval cursor < S then yes.instantiate S cursor
      else no.instantiate S cursor

def Term.disjoin : List (Term Γ σ) → Term Γ σ
  | [] => .const false
  | e :: rest => .or e (disjoin rest)

def Term.mux (condition yes no : Term Γ σ) : Term Γ σ :=
  .or (.and condition yes) (.and (.not condition) no)

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_disjoin (S cursor : Nat) (es : List (Term Γ σ)) :
    (Term.disjoin es).instantiate S cursor =
      Expr.disjoin (es.map (Term.instantiate S cursor)) := by
  induction es <;> simp_all [Term.disjoin, Term.instantiate, Expr.disjoin]

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_mux (S cursor : Nat) (c x y : Term Γ σ) :
    (Term.mux c x y).instantiate S cursor =
      Expr.mux (c.instantiate S cursor) (x.instantiate S cursor) (y.instantiate S cursor) := rfl

noncomputable def finiteTable {A B : Type} [Fintype A] [DecidableEq B]
    (f : A → B) (x : A → Term Γ σ) (b : B) : Term Γ σ :=
  Term.disjoin (Finset.univ.toList.map fun a => .and (x a) (.const (decide (f a = b))))

noncomputable def finiteTable₂ {A B C : Type} [Fintype A] [Fintype B] [DecidableEq C]
    (f : A → B → C) (x : A → Term Γ σ) (y : B → Term Γ σ) (c : C) : Term Γ σ :=
  finiteTable (fun p : A × B => f p.1 p.2) (fun p => .and (x p.1) (y p.2)) c

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_table {A B : Type} [Fintype A] [DecidableEq B]
    (S cursor : Nat) (f : A → B) (x : A → Term Γ σ) (b : B) :
    (finiteTable f x b).instantiate S cursor =
      table f (fun a => (x a).instantiate S cursor) b := by
  simp [finiteTable, table, List.map_map, Term.instantiate, Function.comp_def]

omit [∀ tape, DecidableEq (Γ tape)] in
@[simp] theorem instantiate_table₂ {A B C : Type} [Fintype A] [Fintype B] [DecidableEq C]
    (S cursor : Nat) (f : A → B → C) (x : A → Term Γ σ) (y : B → Term Γ σ) (c : C) :
    (finiteTable₂ f x y c).instantiate S cursor =
      table₂ f (fun a => (x a).instantiate S cursor)
        (fun b => (y b).instantiate S cursor) c := by
  simp [finiteTable₂, table₂, Term.instantiate]

variable {Λ : Type} [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ]

inductive Global where
  | label (value : Option Λ)
  | data (term : Term Γ σ)
  | const (value : Bool)
  | and (left right : Global)
  | or (left right : Global)

def Global.instantiate (S cursor : Nat) : Global (Γ := Γ) (Λ := Λ) (σ := σ) →
    Expr (ConfigBit Γ Λ σ S)
  | .label l => .input (.inl l)
  | .data e => (e.instantiate S cursor).rename Sum.inr
  | .const b => .const b
  | .and e f => .and (e.instantiate S cursor) (f.instantiate S cursor)
  | .or e f => .or (e.instantiate S cursor) (f.instantiate S cursor)

def Global.disjoin : List (Global (Γ := Γ) (Λ := Λ) (σ := σ)) →
    Global (Γ := Γ) (Λ := Λ) (σ := σ)
  | [] => .const false
  | e :: es => .or e (disjoin es)

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] in
@[simp] theorem instantiate_global_disjoin (S cursor : Nat)
    (es : List (Global (Γ := Γ) (Λ := Λ) (σ := σ))) :
    (Global.disjoin es).instantiate S cursor =
      Expr.disjoin (es.map (Global.instantiate S cursor)) := by
  induction es <;> simp_all [Global.disjoin, Global.instantiate, Expr.disjoin]

variable [Fintype Λ]

def outputOrder (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat) :
    List (ConfigBit Γ Λ σ S) :=
  (List.finRange (indexing.width S)).map (indexing.configIndexEquiv S).symm

omit [∀ tape, DecidableEq (Γ tape)] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [∀ tape, Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
@[simp] theorem outputOrder_length (indexing : ConfigIndex.Indexing Γ Λ σ) (S : Nat) :
    (outputOrder indexing S).length = indexing.width S := by
  simp [outputOrder]

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionTemplate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin

@[simp] theorem pairBits_length (input : List Bool × List Bool) :
    (pairBits input).length = 2 * input.1.length + input.2.length + 1 := by
  simp only [pairBits, List.length_append, encodeWord_length]
  omega

noncomputable def NPVerifier.horizon (verifier : NPVerifier) (inputLength : Nat) : Nat :=
  verifier.computation.time.eval
    (2 * inputLength + verifier.witnessBound.eval inputLength + 1)

end BinPackingGames.Foundations.Complexity.CookLevin

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

open scoped BigOperators

abbrev Bits (q : Nat) := Fin (2 * q + 1) → Bool

def selector {q : Nat} (bits : Bits q) (i : Fin (q + 1)) : Bool :=
  bits ⟨i.val, by omega⟩

def payload {q : Nat} (bits : Bits q) (i : Fin q) : Bool :=
  bits ⟨q + 1 + i.val, by omega⟩

def pack {q : Nat} (lengthBits : Fin (q + 1) → Bool)
    (payloadBits : Fin q → Bool) : Bits q := fun i =>
  if h : i.val < q + 1 then lengthBits ⟨i.val, h⟩
  else payloadBits ⟨i.val - (q + 1), by omega⟩

@[simp] theorem selector_pack {q : Nat} (lengthBits : Fin (q + 1) → Bool)
    (payloadBits : Fin q → Bool) (i : Fin (q + 1)) :
    selector (pack lengthBits payloadBits) i = lengthBits i := by
  simp [selector, pack, i.isLt]

@[simp] theorem payload_pack {q : Nat} (lengthBits : Fin (q + 1) → Bool)
    (payloadBits : Fin q → Bool) (i : Fin q) :
    payload (pack lengthBits payloadBits) i = payloadBits i := by
  simp [payload, pack]
  omega

def selectedLength {q : Nat} (bits : Bits q) : Nat :=
  ∑ i : Fin (q + 1), if selector bits i then i.val else 0

theorem selectedLength_eq {q : Nat} (bits : Bits q) (length : Fin (q + 1))
    (h : ∀ i, selector bits i = decide (i = length)) :
    selectedLength bits = length.val := by
  simp [selectedLength, h]

def decode {q : Nat} (bits : Bits q) : List Bool :=
  (List.ofFn (payload bits)).take (selectedLength bits)

def encode (q : Nat) (witness : List Bool) (h : witness.length ≤ q) : Bits q :=
  pack (fun i => decide (i = ⟨witness.length, by omega⟩))
    (fun i => witness[i.val]?.getD false)

@[simp] theorem selector_encode (q : Nat) (witness : List Bool)
    (h : witness.length ≤ q) (i : Fin (q + 1)) :
    selector (encode q witness h) i =
      decide (i = ⟨witness.length, by omega⟩) := by
  simp [encode]

@[simp] theorem payload_encode (q : Nat) (witness : List Bool)
    (h : witness.length ≤ q) (i : Fin q) :
    payload (encode q witness h) i = witness[i.val]?.getD false := by
  simp [encode]

@[simp] theorem selectedLength_encode (q : Nat) (witness : List Bool)
    (h : witness.length ≤ q) : selectedLength (encode q witness h) = witness.length :=
  selectedLength_eq _ ⟨witness.length, by omega⟩ (selector_encode q witness h)

@[simp] theorem decode_encode (q : Nat) (witness : List Bool) (h : witness.length ≤ q) :
    decode (encode q witness h) = witness := by
  unfold decode
  rw [selectedLength_encode]
  apply List.ext_getElem?
  intro n
  by_cases hn : n < witness.length
  · have hnq : n < q := Nat.lt_of_lt_of_le hn h
    simp [hn, hnq]
  · simp [hn]

variable (verifier : NPVerifier) (input : List Bool)

def initial (bits : Bits (verifier.witnessBound.eval input.length)) :
    verifier.computation.tm.Cfg :=
  Turing.initList verifier.computation.tm
    ((pairBits (input, decode bits)).map verifier.computation.inputAlphabet.invFun)

@[simp] theorem initial_control (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).l = some verifier.computation.tm.main := rfl

@[simp] theorem initial_state (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).var = verifier.computation.tm.initialState := rfl

@[simp] theorem initial_input_stack (bits : Bits (verifier.witnessBound.eval input.length)) :
    (initial verifier input bits).stk verifier.computation.tm.k₀ =
      (pairBits (input, decode bits)).map verifier.computation.inputAlphabet.invFun := by
  simp [initial, Turing.initList]

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessEncoding

namespace BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

open StatementCircuit WitnessEncoding

def selectorExpr (q : Nat) (i : Fin (q + 1)) : Expr (Fin (2 * q + 1)) :=
  .input ⟨i.val, by omega⟩

def payloadExpr (q : Nat) (i : Fin q) : Expr (Fin (2 * q + 1)) :=
  .input ⟨q + 1 + i.val, by omega⟩

@[simp] theorem eval_selectorExpr {q : Nat} (bits : Bits q) (i : Fin (q + 1)) :
    (selectorExpr q i).eval bits = selector bits i := rfl

@[simp] theorem eval_payloadExpr {q : Nat} (bits : Bits q) (i : Fin q) :
    (payloadExpr q i).eval bits = payload bits i := rfl

section Size

@[simp] theorem size_selectorExpr (q : Nat) (i : Fin (q + 1)) :
    (selectorExpr q i).size = 1 := rfl

@[simp] theorem size_payloadExpr (q : Nat) (i : Fin q) :
    (payloadExpr q i).size = 1 := rfl

end Size

end BinPackingGames.Foundations.Complexity.CookLevin.WitnessCircuit

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

open Turing StatementCircuit CircuitBatch
open scoped BigOperators

local instance alphabetFinite (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) :=
  V.finiteAlphabet
local instance labelFinite_r9defb6_1 (V : NPVerifier) : Fintype V.computation.tm.Λ :=
  V.computation.tm.ΛFin
local instance stateFinite_r9defb6_1 (V : NPVerifier) : Fintype V.computation.tm.σ :=
  V.computation.tm.σFin
local instance labelDecidable (V : NPVerifier) : DecidableEq V.computation.tm.Λ :=
  Classical.decEq _
local instance stateDecidable (V : NPVerifier) : DecidableEq V.computation.tm.σ :=
  Classical.decEq _
local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def capacity (V : NPVerifier) (n : Nat) : Nat :=
  2 * n + V.witnessBound.eval n + 1 + V.horizon n * Runtime.programPushBound V.computation.tm

abbrev Bit (V : NPVerifier) (input : List Bool) :=
  ConfigBit V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ (capacity V input.length)

def indexing (V : NPVerifier) :
    ConfigIndex.Indexing V.computation.tm.Γ V.computation.tm.Λ V.computation.tm.σ :=
  ConfigIndex.ofMachine V.computation.tm

abbrev width (V : NPVerifier) (input : List Bool) : Nat :=
  (indexing V).width (capacity V input.length)

def bitEquiv (V : NPVerifier) (input : List Bool) : Bit V input ≃ Fin (width V input) :=
  (indexing V).configIndexEquiv (capacity V input.length)

def bitWire (V : NPVerifier) (input : List Bool) (b : Bit V input) : Fin (width V input + 1) :=
  (bitEquiv V input b).castSucc

def stateEncoding (V : NPVerifier) (input : List Bool) (cfg : V.computation.tm.Cfg)
    (valid : Bool) : Fin (width V input + 1) → Bool :=
  Fin.lastCases valid (fun j => configEncoding (capacity V input.length) cfg
    ((bitEquiv V input).symm j))

@[simp] theorem stateEncoding_last (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool) :
    stateEncoding V input cfg valid (Fin.last (width V input)) = valid := by
  simp [stateEncoding]

@[simp] theorem stateEncoding_bitWire (V : NPVerifier) (input : List Bool)
    (cfg : V.computation.tm.Cfg) (valid : Bool) (b : Bit V input) :
    stateEncoding V input cfg valid (bitWire V input b) =
      configEncoding (capacity V input.length) cfg b := by
  simp [stateEncoding, bitWire]

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierCircuit

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_NormalizationEmitMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingCompleteness.SourceClause

open BinPackingGames.Foundations.Target

abbrev Triple := Bool × Bool × Bool

def literalTruth (positive value : Bool) : Bool :=
  if positive then value else !value

def localEval (signs values : Triple) : Bool :=
  (literalTruth signs.1 values.1 || literalTruth signs.2.1 values.2.1) ||
    literalTruth signs.2.2 values.2.2

structure NormalizedClause («variables» : Nat) where
  clause : Clause «variables»
  distinct : ∀ i j : Fin 3,
    clause[i].variableIndex = clause[j].variableIndex → i = j

def NormalizedClause.variable {n : Nat} (c : NormalizedClause n) (i : Fin 3) : Fin n :=
  c.clause[i].variableIndex

def NormalizedClause.signs {n : Nat} (c : NormalizedClause n) : Triple :=
  (c.clause[0].positive, c.clause[1].positive, c.clause[2].positive)

def NormalizedClause.restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) : Triple :=
  (assignment (c.variable 0), assignment (c.variable 1), assignment (c.variable 2))

@[simp] theorem localEval_restrict {n : Nat} (c : NormalizedClause n)
    (assignment : Fin n → Bool) :
    localEval c.signs (c.restrict assignment) = c.clause.eval assignment := by
  rfl

end BinPackingCompleteness.SourceClause

namespace BinPackingCompleteness.Normalization

open BinPackingGames.Foundations
open Target
open SourceClause

def tripleClause {n : Nat} (a b c : Fin n) (sa sb sc : Bool) : Clause n :=
  #v[⟨a, sa⟩, ⟨b, sb⟩, ⟨c, sc⟩]

def normalizedTriple {n : Nat} (a b c : Fin n) (sa sb sc : Bool)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : NormalizedClause n where
  clause := tripleClause a b c sa sb sc
  distinct := by
    intro i j h
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi with rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl <;>
      simp_all [tripleClause]

def outputVariables (F : Formula) : Nat := F.variables + 4 * F.clauses.length

def oldVariable (F : Formula) (v : Fin F.variables) : Fin (outputVariables F) :=
  ⟨v.val, by have := v.isLt; unfold outputVariables; omega⟩

def freshVariable (F : Formula) (c : Fin F.clauses.length) (i : Fin 4) :
    Fin (outputVariables F) :=
  ⟨F.variables + 4 * c.val + i.val, by
    have hc := c.isLt
    have hi := i.isLt
    unfold outputVariables
    omega⟩

def copyVariable (F : Formula) (c : Fin F.clauses.length) (i : Fin 3) :
    Fin (outputVariables F) :=
  freshVariable F c ⟨i.val, by have := i.isLt; omega⟩

def paddingVariable (F : Formula) (c : Fin F.clauses.length) :
    Fin (outputVariables F) := freshVariable F c 3

theorem copy_ne_copy (F : Formula) (c : Fin F.clauses.length)
    {i j : Fin 3} (hij : i ≠ j) : copyVariable F c i ≠ copyVariable F c j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [copyVariable, freshVariable] at hv
  apply hij
  apply Fin.ext
  omega

theorem copy_ne_old (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) (v : Fin F.variables) : copyVariable F c i ≠ oldVariable F v := by
  intro h
  have hv := congrArg Fin.val h
  have hvlt := v.isLt
  dsimp [copyVariable, freshVariable, oldVariable] at hv
  omega

theorem copy_ne_padding (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) : copyVariable F c i ≠ paddingVariable F c := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  dsimp [copyVariable, paddingVariable, freshVariable] at hv
  omega

theorem old_ne_padding (F : Formula) (c : Fin F.clauses.length)
    (v : Fin F.variables) : oldVariable F v ≠ paddingVariable F c := by
  intro h
  have hv := congrArg Fin.val h
  have hvlt := v.isLt
  dsimp [paddingVariable, freshVariable, oldVariable] at hv
  omega

def mainClause (F : Formula) (c : Fin F.clauses.length) :
    NormalizedClause (outputVariables F) :=
  normalizedTriple (copyVariable F c 0) (copyVariable F c 1) (copyVariable F c 2)
    (PCP.clauseAt F c)[0].positive (PCP.clauseAt F c)[1].positive
    (PCP.clauseAt F c)[2].positive
    (copy_ne_copy F c (by decide)) (copy_ne_copy F c (by decide))
    (copy_ne_copy F c (by decide))

def equalityClauses (F : Formula) (c : Fin F.clauses.length) (i : Fin 3) :
    List (NormalizedClause (outputVariables F)) :=
  let x := copyVariable F c i
  let v := oldVariable F (PCP.clauseAt F c)[i].variableIndex
  let z := paddingVariable F c
  let hxv := copy_ne_old F c i (PCP.clauseAt F c)[i].variableIndex
  let hxz := copy_ne_padding F c i
  let hvz := old_ne_padding F c (PCP.clauseAt F c)[i].variableIndex
  [normalizedTriple x v z false true true hxv hxz hvz,
   normalizedTriple x v z false true false hxv hxz hvz,
   normalizedTriple x v z true false true hxv hxz hvz,
   normalizedTriple x v z true false false hxv hxz hvz]

def gadget (F : Formula) (c : Fin F.clauses.length) :
    List (NormalizedClause (outputVariables F)) :=
  [mainClause F c] ++ equalityClauses F c 0 ++
    equalityClauses F c 1 ++ equalityClauses F c 2

def gadgetClauses (F : Formula) (c : Fin F.clauses.length) :
    List (Clause (outputVariables F)) :=
  (gadget F c).map NormalizedClause.clause

@[simp] theorem equalityClauses_length (F : Formula) (c : Fin F.clauses.length)
    (i : Fin 3) : (equalityClauses F c i).length = 4 := rfl

@[simp] theorem gadget_length (F : Formula) (c : Fin F.clauses.length) :
    (gadget F c).length = 13 := by simp [gadget]

@[simp] theorem gadgetClauses_length (F : Formula) (c : Fin F.clauses.length) :
    (gadgetClauses F c).length = 13 := by simp [gadgetClauses]

def restrictAssignment (F : Formula) (B : Fin (outputVariables F) → Bool) :
    Fin F.variables → Bool := fun v => B (oldVariable F v)

def extendAssignment (F : Formula) (A : Fin F.variables → Bool)
    (v : Fin (outputVariables F)) : Bool :=
  if old : v.val < F.variables then A ⟨v.val, old⟩
  else
    let c : Fin F.clauses.length := ⟨(v.val - F.variables) / 4, by
      have hv := v.isLt
      unfold outputVariables at hv
      omega⟩
    if slot : (v.val - F.variables) % 4 < 3 then
      A (PCP.clauseAt F c)[(⟨(v.val - F.variables) % 4, slot⟩ : Fin 3)].variableIndex
    else false

@[simp] theorem extend_oldVariable (F : Formula) (A : Fin F.variables → Bool)
    (v : Fin F.variables) : extendAssignment F A (oldVariable F v) = A v := by
  simp [extendAssignment, oldVariable, v.isLt]

@[simp] theorem extend_copyVariable (F : Formula) (A : Fin F.variables → Bool)
    (c : Fin F.clauses.length) (i : Fin 3) :
    extendAssignment F A (copyVariable F c i) = A (PCP.clauseAt F c)[i].variableIndex := by
  have hi := i.isLt
  have hold : ¬ F.variables + 4 * c.val + i.val < F.variables := by omega
  have hdiv : (F.variables + 4 * c.val + i.val - F.variables) / 4 = c.val := by omega
  have hmod : (F.variables + 4 * c.val + i.val - F.variables) % 4 = i.val := by omega
  simp [extendAssignment, copyVariable, freshVariable, hold, hdiv, hmod, hi]

@[simp] theorem restrict_extend (F : Formula) (A : Fin F.variables → Bool) :
    restrictAssignment F (extendAssignment F A) = A := by
  funext v
  exact extend_oldVariable F A v

def normalizedClauses (F : Formula) : List (NormalizedClause (outputVariables F)) :=
  (PCP.allIndices F).flatMap (gadget F)

def normalize (F : Formula) : Formula where
  «variables» := outputVariables F
  clauses := (PCP.allIndices F).flatMap (gadgetClauses F)

theorem normalize_clauses_eq_map (F : Formula) :
    (normalize F).clauses = (normalizedClauses F).map NormalizedClause.clause := by
  simp only [normalize, normalizedClauses, List.map_flatMap]
  rfl

theorem normalize_distinct (F : Formula) (c : Clause (normalize F).variables)
    (hc : c ∈ (normalize F).clauses) (i j : Fin 3)
    (same : (c)[i].variableIndex = (c)[j].variableIndex) : i = j := by
  rw [normalize_clauses_eq_map] at hc
  obtain ⟨d, _, hd⟩ := List.mem_map.mp hc
  subst c
  exact d.distinct i j same

@[simp] theorem normalize_variables (F : Formula) :
    (normalize F).variables = F.variables + 4 * F.clauses.length := rfl

@[simp] theorem normalize_clause_count (F : Formula) :
    (normalize F).clauses.length = 13 * F.clauses.length := by
  change ((PCP.allIndices F).flatMap (gadgetClauses F)).length = _
  rw [PCP.VerifierToCNF.length_flatMap_constant _ _ 13
    (fun c _ => gadgetClauses_length F c)]
  simp [PCP.allIndices, Nat.mul_comm]

theorem normalize_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    (normalize F).clauses ≠ [] := by
  have hm : 0 < F.clauses.length := List.length_pos_iff.mpr hne
  have hout : 0 < (normalize F).clauses.length := by
    rw [normalize_clause_count]
    omega
  exact List.ne_nil_of_length_pos hout

end BinPackingCompleteness.Normalization

namespace BinPackingCompleteness.NormalizationWords

open BinPackingGames.Foundations
open Complexity

abbrev Signs := Fin 3 → Bool
abbrev Names := Fin 3 → Nat

inductive NameRef
  | old (slot : Fin 3)
  | fresh (slot : Fin 4)
  deriving DecidableEq, Fintype

inductive SignRef
  | source (slot : Fin 3)
  | constant (sign : Bool)
  deriving DecidableEq, Fintype

structure LiteralRecipe where
  name : NameRef
  sign : SignRef
  deriving DecidableEq, Fintype

def sourceValue (names : Names) (freshBase : Nat) : NameRef → Nat
  | .old i => names i
  | .fresh _ => freshBase

def signValue (signs : Signs) : SignRef → Bool
  | .source i => signs i
  | .constant sign => sign

def mainRecipe : List LiteralRecipe :=
  [⟨.fresh 0, .source 0⟩, ⟨.fresh 1, .source 1⟩, ⟨.fresh 2, .source 2⟩]

def equalityRecipe (i : Fin 3) : List LiteralRecipe :=
  [⟨.fresh i.castSucc, .constant false⟩, ⟨.old i, .constant true⟩, ⟨.fresh 3, .constant true⟩,
   ⟨.fresh i.castSucc, .constant false⟩, ⟨.old i, .constant true⟩, ⟨.fresh 3, .constant false⟩,
   ⟨.fresh i.castSucc, .constant true⟩, ⟨.old i, .constant false⟩, ⟨.fresh 3, .constant true⟩,
   ⟨.fresh i.castSucc, .constant true⟩, ⟨.old i, .constant false⟩, ⟨.fresh 3, .constant false⟩]

def recipe : List LiteralRecipe :=
  mainRecipe ++ equalityRecipe 0 ++ equalityRecipe 1 ++ equalityRecipe 2

@[simp] theorem recipe_length : recipe.length = 39 := by decide

end BinPackingCompleteness.NormalizationWords

namespace BinPackingCompleteness.NormalizationEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open NormalizationWords

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Signs) × Option Bool

def clean (ambient : A) (signs : Signs) : State A := ((ambient, signs), none)

inductive LocalLabel
  | copyOut
  | copyBack
  | emit
  deriving DecidableEq

protected abbrev LocalLabel.enumList : List LocalLabel := [.copyOut, .copyBack, .emit]

protected theorem LocalLabel.enumList_nodup : LocalLabel.enumList.Nodup := by decide

def cost (names : Names) (freshBase : Nat) (literal : LiteralRecipe) (_ : List Bool) : Nat :=
  2 * (sourceValue names freshBase literal.name + 1) + 1

def commandSteps (names : Names) (freshBase : Nat) (commands : List LiteralRecipe) : Nat :=
  (commands.map (fun literal => 2 * (sourceValue names freshBase literal.name + 1) + 1)).sum

theorem sourceValue_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (name : NameRef) : sourceValue names freshBase name ≤ maximum := by
  cases name with
  | old i => exact nameBounds i
  | fresh i => exact freshBound

theorem commandSteps_le (names : Names) (freshBase maximum : Nat)
    (freshBound : freshBase ≤ maximum) (nameBounds : ∀ i, names i ≤ maximum)
    (commands : List LiteralRecipe) :
    commandSteps names freshBase commands ≤ commands.length * (2 * maximum + 3) := by
  induction commands with
  | nil => simp [commandSteps]
  | cons literal commands ih =>
      have current := sourceValue_le names freshBase maximum freshBound nameBounds literal.name
      simp only [commandSteps, List.map_cons, List.sum_cons, List.length_cons,
        Nat.add_mul, Nat.one_mul] at ih ⊢
      omega

abbrev Labels (commands : List LiteralRecipe) :=
  MachineFiniteSequence.Label (fun _ : LiteralRecipe => LocalLabel) commands

abbrev Label := Labels recipe

end BinPackingCompleteness.NormalizationEmitMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_BinaryHeaderMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingCompleteness.BinaryHeaderMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

@[simp] theorem tapes_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output variableTape =
      variableCounter := by
  simp [tapes, vc, vd]

@[simp] theorem tapes_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output clauses =
      clauseCounter := by
  simp [tapes, cd]

@[simp] theorem tapes_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output destination =
      output := by
  simp [tapes]

theorem update_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      variableTape replacement = tapes variableTape clauses destination base replacement clauseCounter output := by
  funext k
  by_cases hv : k = variableTape
  · subst k
    simp [tapes, vc, vd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hv]
    · by_cases hc : k = clauses
      · subst k
        simp [tapes, hv, hd]
      · simp [tapes, hv, hc, hd]

theorem update_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      clauses replacement = tapes variableTape clauses destination base variableCounter replacement output := by
  funext k
  by_cases hc : k = clauses
  · subst k
    simp [tapes, cd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hc]
    · simp [tapes, hc, hd]

theorem update_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      destination replacement = tapes variableTape clauses destination base variableCounter clauseCounter replacement := by
  simp [tapes]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atClauseLoop : program clauseLoop =
  loopAt clauses destination id false clauseLoop (some variableStart))
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (atVariableLoop : program variableLoop =
  loopAt variableTape destination id false variableLoop exit)
variable (base : K → List Bool) (ambient : A)

include atClauseStart in
theorem clauseDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some clauseLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program clauseStart) _ _) = _
  rw [atClauseStart]
  simp [delimiter, TM2.stepAux, update_destination]

include atVariableStart in
theorem variableDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some variableStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some variableLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program variableStart) _ _) = _
  rw [atVariableStart]
  simp [delimiter, TM2.stepAux, update_destination]

include cd atClauseLoop in
theorem clauseCounterTrace (m : Nat) (variableCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some clauseLoop, (ambient, register),
        tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) =
      some ⟨some variableStart, (ambient, none),
        tapes variableTape clauses destination base variableCounter [] (List.replicate m true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) clauses destination cd id false
    clauseLoop (some variableStart) program atClauseLoop
    (tapes variableTape clauses destination base variableCounter (List.replicate m true) output)
    ambient register
  change (nextAt destination program)^[m + 1]
    (some ⟨some clauseLoop, (ambient, register),
      tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) = _
  simpa only [tapes_clauses variableTape clauses destination cd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_clauses variableTape clauses destination cd, update_destination,
    nextAt, advance] using h

include vc vd atVariableLoop in
theorem variableCounterTrace (n : Nat) (clauseCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[n + 1]
      (some ⟨some variableLoop, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] clauseCounter (List.replicate n true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) variableTape destination vd id false
    variableLoop exit program atVariableLoop
    (tapes variableTape clauses destination base (List.replicate n true) clauseCounter output)
    ambient register
  change (nextAt destination program)^[n + 1]
    (some ⟨some variableLoop, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) = _
  simpa only [tapes_variables variableTape clauses destination vc vd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_variables variableTape clauses destination vc vd, update_destination,
    nextAt, advance] using h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

include vc vd cd atClauseStart atClauseLoop atVariableStart atVariableLoop

theorem headerTrace (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := clauseDelimiterStep variableTape clauses destination clauseStart clauseLoop program
    atClauseStart base ambient (List.replicate n true) (List.replicate m true) body register
  change (advance (TM2.step program))^[1]
    (some ⟨some clauseStart, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩) = _ at first
  have second := clauseCounterTrace variableTape clauses destination cd clauseLoop variableStart program
    atClauseLoop base ambient m (List.replicate n true) (false :: body) none
  have third := variableDelimiterStep variableTape clauses destination variableStart variableLoop program
    atVariableStart base ambient (List.replicate n true) []
    (List.replicate m true ++ false :: body) none
  change (advance (TM2.step program))^[1]
    (some ⟨some variableStart, (ambient, none),
      tapes variableTape clauses destination base (List.replicate n true) []
        (List.replicate m true ++ false :: body)⟩) = _ at third
  have fourth := variableCounterTrace variableTape clauses destination vc vd variableLoop exit program
    atVariableLoop base ambient n [] (false :: (List.replicate m true ++ false :: body)) none
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  have htime : ((1 + (m + 1)) + 1) + (n + 1) = n + m + 4 := by omega
  rw [htime] at full
  simpa only [encodeWord, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] using full

end Placement

end BinPackingCompleteness.BinaryHeaderMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_BinaryNameCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingCompleteness.BinaryNameMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source, update_destination]

theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

end BinPackingCompleteness.BinaryNameMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_BinaryPairMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingCompleteness.BinaryPairMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer

abbrev Tape := Fin 3
abbrev Label := Fin 5
abbrev State := Unit × Option Bool
abbrev Alphabet (_ : Tape) := Bool

def stop (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

def count : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (stop 4)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true) (.goto fun _ => 0))
        (stop 1)))

def copy : TM2.Stmt Alphabet Label State :=
  .pop 1 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false) (.goto fun _ => 1))
          (stop 4)))
      (stop 2))

def program (label : Label) : TM2.Stmt Alphabet Label State :=
  if label = 0 then count
  else if label = 1 then copy
  else if label = 2 then loopAt 2 1 id false 2 (some 3)
  else .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := 0
  σ := State
  initialState := ((), none)
  m := program

def tapes (input counter saved : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then counter else saved

def cfg (label : Option Label) (input counter saved : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input counter saved⟩

@[simp] theorem tapes_zero (input counter saved : List Bool) :
    tapes input counter saved 0 = input := rfl

@[simp] theorem tapes_one (input counter saved : List Bool) :
    tapes input counter saved 1 = counter := rfl

@[simp] theorem tapes_two (input counter saved : List Bool) :
    tapes input counter saved 2 = saved := rfl

theorem update_zero (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 0 replacement =
      tapes replacement counter saved := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_one (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_two (input counter saved replacement : List Bool) :
    Function.update (tapes input counter saved) 2 replacement =
      tapes input counter replacement := by
  funext k
  fin_cases k <;> simp [tapes]

theorem countStep_true (input counter saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 0) (true :: input) counter saved register) =
      some (cfg (some 0) input (true :: counter) saved (some true)) := by
  change some (TM2.stepAux (program 0) _ _) = _
  simp [program, count, cfg, TM2.stepAux, update_zero, update_one]
  all_goals rfl

theorem countStep_false (input counter saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 0) (false :: input) counter saved register) =
      some (cfg (some 1) input counter saved) := by
  change some (TM2.stepAux (program 0) _ _) = _
  simp [program, count, stop, cfg, TM2.stepAux, update_zero]
  all_goals rfl

theorem countTrace (n : Nat) (input counter saved : List Bool) (register : Option Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some 0) (encodeWord n ++ input) counter saved register)) =
      some (cfg (some 1) input (List.replicate n true ++ counter) saved) := by
  induction n generalizing counter register with
  | zero =>
      simpa only [Nat.zero_add, Function.iterate_one, advance_some, encodeWord,
        List.replicate_zero, List.nil_append, List.singleton_append] using
        countStep_false input counter saved register
  | succ n ih =>
      rw [show encodeWord (n + 1) ++ input = true :: (encodeWord n ++ input) by
        simp only [encodeWord, List.replicate_succ, List.cons_append]]
      rw [Function.iterate_succ_apply]
      simp only [advance_some]
      rw [countStep_true]
      rw [ih]
      rw [List.replicate_succ']
      simp only [List.append_assoc, List.singleton_append]

theorem copyStep_empty (input saved : List Bool) (register : Option Bool) :
    machine.step (cfg (some 1) input [] saved register) =
      some (cfg (some 2) input [] saved) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, copy, stop, cfg, TM2.stepAux, update_one]
  all_goals rfl

theorem copyStep_cons (bit : Bool) (input counter saved : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some 1) (bit :: input) (true :: counter) saved register) =
      some (cfg (some 1) input counter (bit :: saved) (some bit)) := by
  change some (TM2.stepAux (program 1) _ _) = _
  simp [program, copy, cfg, TM2.stepAux, update_zero, update_one, update_two]
  all_goals rfl

theorem copyTrace (input suffix saved : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 1) (input ++ suffix) (List.replicate input.length true) saved register)) =
      some (cfg (some 2) suffix [] (input.reverse ++ saved)) := by
  induction input generalizing saved register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.nil_append, List.replicate_zero, List.reverse_nil] using
        copyStep_empty suffix saved register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [List.cons_append, List.replicate_succ, advance_some]
      rw [copyStep_cons, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem restoreTrace (input witness : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some 2) witness [] input.reverse register)) =
      some (cfg (some 3) witness input []) := by
  change (nextAt (Γ := Alphabet) (1 : Tape) program)^[input.length + 1]
    (some ⟨some (2 : Label), ((), register), tapes witness [] input.reverse⟩) =
    some ⟨some (3 : Label), ((), none), tapes witness input []⟩
  have h := transferAt_steps (Γ := Alphabet) (σ := Unit) (2 : Tape) 1 (by decide)
    id false (2 : Label) (some 3) program (by simp [program])
    (tapes witness [] []) input.reverse [] () register
  simpa only [tapesAt, update_two, update_one, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, List.append_nil] using h

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some 0) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem pairTrace (input witness : List Bool) :
    (advance machine.step)^[3 * input.length + 3]
      (some (initList machine (CookLevin.pairBits (input, witness)))) =
      some (cfg (some 3) witness input []) := by
  have first := countTrace input.length (input ++ witness) [] [] none
  simp only [List.append_nil] at first
  have second := copyTrace input witness [] none
  simp only [List.append_nil] at second
  have third := restoreTrace input witness none
  have full := joinTrace (joinTrace first second) third
  have htime : (input.length + 1 + (input.length + 1)) + (input.length + 1) =
      3 * input.length + 3 := by omega
  rw [htime] at full
  simpa only [initList_eq, CookLevin.pairBits, List.append_assoc] using full

theorem haltStep (input witness : List Bool) :
    machine.step (cfg (some 3) witness input []) = some (cfg none witness input []) := by
  change some (TM2.stepAux (program 3) _ _) = _
  simp [program, cfg, TM2.stepAux]
  all_goals rfl

def pairHaltInTime (input witness : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (CookLevin.pairBits (input, witness)))
      (some (cfg none witness input [])) (3 * input.length + 4) where
  steps := 3 * input.length + 4
  evals_in_steps := by
    change (advance machine.step)^[3 * input.length + 4]
      (some (initList machine (CookLevin.pairBits (input, witness)))) = _
    rw [show 3 * input.length + 4 = (3 * input.length + 3) + 1 by omega,
      Function.iterate_succ_apply', pairTrace, advance_some, haltStep]
  steps_le_m := Nat.le_refl _

end BinPackingCompleteness.BinaryPairMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Reductions_BinaryTokenMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingCompleteness.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

end BinPackingCompleteness.BinaryEncoding

namespace BinPackingCompleteness.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [BinaryNameMachine.frame, frame, ih]

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

end BinPackingCompleteness.BinaryParsing

end OAI
end


