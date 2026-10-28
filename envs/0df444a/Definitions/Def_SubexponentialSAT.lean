-- Prove2me | Definitions.Def_SubexponentialSAT
-- name    : SubexponentialSAT
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T10:02:49.468465+00:00
-- url     : https://prove2.me/theorems/a8e77990-3194-42f4-9b21-02bc9ee2b0c2
-- title:
--   CNF formulas, their bit encoding, and a primitive multi-tape machine with visited-space accounting (OpenAI's subexponential SAT challenge)
-- statement:
--   The definitions of OpenAI's comparator challenge for result family 378, "Disproof of the Exponential Time Hypothesis", copied unchanged from `lean/ComparatorChallenges/SubexponentialSAT.lean` (everything before the theorem). The statement `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` uses them.
--
--   **Formulas** (`SAT`). A literal over a variable type $V$ is a variable with a sign; a clause is a finite set of literals and a CNF formula a finite set of clauses. An assignment $V \to \mathrm{Bool}$ satisfies a literal when the variable's value equals its sign, a clause when some literal is satisfied, and a formula when every clause is. `WidthAtMost k F` says every clause has at most $k$ literals. For finite $V$, `satisfyingAssignments F` is the finite set of satisfying assignments and `count F` its cardinality.
--
--   **Encoding** (`Encoding`). A natural number $n$ is written in unary, $n$ ones then a zero; a list of bit strings is framed so that it can be read back unambiguously. A literal on variable $i$ is the number $2i+1$ if positive and $2i$ if negative; a clause is the sorted list of its literal numbers and a formula the sorted list of its clauses. `encodeCNF F` for a formula on $n$ variables is the unary code of $n$ followed by the framed encoding of that list, and `formulaBitLength F` is its length.
--
--   **Machines** (`Computation`). A `PrimitiveMachine` has finitely many tapes over the alphabet $\{\text{blank}, 0, 1\}$, finitely many states, an input tape and a start state. Each state scans one tape and, on the symbol under that tape's head, either halts with a Boolean answer or moves to a new state while moving that head one cell or writing one symbol (a `Turing.TM0.Stmt`). A configuration is a state (running, or halted with an answer) and the contents of all tapes; `init` puts the input on the input tape, every other tape blank. `Trace step t a b` says that $t$ steps lead from $a$ to $b$.
--
--   **Bounds and space** (`SqrtLog.Statement`, `SqrtLogSpace`). `runtimeScale n` is $n\,(\log\log(n+16))^2/\sqrt{\log(n+16)}$, and `runtimeBound C A d L n` is $C\,(L+1)^d\,2^{A\cdot\text{runtimeScale}(n)}$. A located configuration also records, for every tape, the head position and the lowest and highest cells the head has visited; `locatedStep` runs one machine step while updating these, and `visitedSpace` is the total number of visited cells over all tapes. `countWord a` is the binary representation of $a$, least significant bit first (`[false]` for zero), and `BinaryArithmetic.toNat` reads such a word back.
-- source:
--   OpenAI, "The Exponential Time Hypothesis is False" (preprint, October 25, 2026), OpenAI Math Release 2026-10-26, https://github.com/openai/math (result family 378); comparator challenge https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/ComparatorChallenges/SubexponentialSAT.lean, Apache License 2.0

import Mathlib

namespace OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

def bitVal (b : Bool) : ℕ := if b then 1 else 0

def toNat : List Bool → ℕ
  | [] => 0
  | b :: bs => bitVal b + 2 * toNat bs

end OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms.SubexponentialSAT.SAT

universe u

abbrev Assignment (V : Type u) := V → Bool

structure Literal (V : Type u) where
  «variable» : V
  positive : Bool
  deriving DecidableEq

abbrev Clause (V : Type u) := Finset (Literal V)
abbrev CNF (V : Type u) := Finset (Clause V)

variable {V : Type u} [DecidableEq V]

def Literal.eval (a : Assignment V) (l : Literal V) : Bool :=
  a l.variable == l.positive

def Clause.eval (a : Assignment V) (C : Clause V) : Bool :=
  decide (∃ l ∈ C, l.eval a = true)

def CNF.eval (a : Assignment V) (F : CNF V) : Bool :=
  decide (∀ C ∈ F, C.eval a = true)

def WidthAtMost (k : ℕ) (F : CNF V) : Prop := ∀ C ∈ F, C.card ≤ k

section Finite

variable [Fintype V]

def satisfyingAssignments (F : CNF V) : Finset (Assignment V) :=
  Finset.univ.filter fun a => F.eval a = true

def count (F : CNF V) : ℕ := (satisfyingAssignments F).card

end Finite

end OAI.Algorithms.SubexponentialSAT.SAT

namespace OAI.Algorithms.SubexponentialSAT.Encoding

def encodeNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

def frame (bits : List Bool) : List Bool :=
  bits.foldr (fun b rest => true :: b :: rest) [false]

def encodeList {α : Type*} (enc : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: as => true :: (frame (enc a) ++ encodeList enc as)

def literalCode {n : ℕ} (l : SAT.Literal (Fin n)) : ℕ :=
  2 * l.variable.val + if l.positive then 1 else 0

def clauseNumbers {n : ℕ} (C : SAT.Clause (Fin n)) : List ℕ :=
  (C.image literalCode).sort (· ≤ ·)

def cnfNumbers {n : ℕ} (F : SAT.CNF (Fin n)) : List (List ℕ) :=
  (F.image clauseNumbers).sort (· ≤ ·)

def encodeCNFBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeList (encodeList encodeNat) (cnfNumbers F)

def encodeCNF {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  encodeNat n ++ encodeCNFBody F

def formulaBitLength {n : ℕ} (F : SAT.CNF (Fin n)) : ℕ := (encodeCNF F).length

end OAI.Algorithms.SubexponentialSAT.Encoding

namespace OAI.Algorithms.SubexponentialSAT.Computation

universe u

inductive Trace {α : Type u} (step : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace step 0 a a
  | cons {n : ℕ} {a b c : α} :
      step a = some b → Trace step n b c → Trace step (n + 1) a c

structure PrimitiveMachine where
  tapeCount : ℕ
  stateCount : ℕ
  inputTape : Fin tapeCount
  start : Fin stateCount
  scan : Fin stateCount → Fin tapeCount
  transition : Fin stateCount → Option Bool →
    Bool ⊕ (Fin stateCount × Turing.TM0.Stmt (Option Bool))

namespace PrimitiveMachine

structure Cfg (machine : PrimitiveMachine) where
  state : Bool ⊕ Fin machine.stateCount
  tapes : Fin machine.tapeCount → Turing.Tape (Option Bool)

def step (machine : PrimitiveMachine) (c : machine.Cfg) : Option machine.Cfg :=
  match c.state with
  | .inl _ => none
  | .inr q =>
    let tapeIndex := machine.scan q
    match machine.transition q (c.tapes tapeIndex).head with
    | .inl answer => some ⟨.inl answer, c.tapes⟩
    | .inr (q', action) =>
      let nextTape :=
        match action with
        | .move direction => (c.tapes tapeIndex).move direction
        | .write symbol => (c.tapes tapeIndex).write symbol
      some ⟨.inr q', Function.update c.tapes tapeIndex nextTape⟩

def init (machine : PrimitiveMachine) (input : List Bool) : machine.Cfg :=
  ⟨.inr machine.start, fun k =>
    if k = machine.inputTape then Turing.Tape.mk₁ (input.map some)
    else Turing.Tape.mk₁ []⟩

end PrimitiveMachine

end OAI.Algorithms.SubexponentialSAT.Computation

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement

noncomputable def runtimeScale (n : ℕ) : ℝ :=
  (n : ℝ) * (Real.log (Real.log ((n : ℝ) + 16))) ^ 2 /
    Real.sqrt (Real.log ((n : ℝ) + 16))

noncomputable def runtimeBound (constant exponentConstant : ℝ)
    (degree inputBits numVars : ℕ) : ℝ :=
  constant * ((inputBits : ℝ) + 1) ^ degree *
    (2 : ℝ) ^ (exponentConstant * runtimeScale numVars)

end OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open OAI.Algorithms.SubexponentialSAT.Computation

def countWord (a : ℕ) : List Bool := if a = 0 then [false] else a.bits

structure LocatedCfg (machine : PrimitiveMachine) where
  config : machine.Cfg
  position : Fin machine.tapeCount → ℤ
  lower : Fin machine.tapeCount → ℤ
  upper : Fin machine.tapeCount → ℤ

def locatedInit (machine : PrimitiveMachine) (input : List Bool) : LocatedCfg machine where
  config := machine.init input
  position _ := 0
  lower _ := 0
  upper i := if i = machine.inputTape then Int.ofNat (input.length - 1) else 0

def headDisplacement : Turing.TM0.Stmt (Option Bool) → ℤ
  | .move .left => -1
  | .move .right => 1
  | .write _ => 0

def LocatedCfg.monitor {machine : PrimitiveMachine} (c : LocatedCfg machine)
    (config : machine.Cfg) : LocatedCfg machine :=
  Sum.elim
    (fun _ => { c with config })
    (fun q =>
      Sum.elim
        (fun _ => { c with config })
        (fun targetAction =>
          let action := targetAction.2
          let i := machine.scan q
          let position := c.position i + headDisplacement action
          { config
            position := Function.update c.position i position
            lower := Function.update c.lower i (min (c.lower i) position)
            upper := Function.update c.upper i (max (c.upper i) position) })
        (machine.transition q (c.config.tapes (machine.scan q)).head))
    c.config.state

def locatedStep (machine : PrimitiveMachine) (c : LocatedCfg machine) :
    Option (LocatedCfg machine) :=
  (machine.step c.config).map c.monitor

def visitedSpace {machine : PrimitiveMachine} (c : LocatedCfg machine) : ℕ :=
  ∑ i, (c.upper i - c.lower i + 1).toNat

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


