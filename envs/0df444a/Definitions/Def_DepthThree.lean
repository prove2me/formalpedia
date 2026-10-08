-- Prove2me | Definitions.Def_DepthThree
-- name    : DepthThree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.501679+00:00
-- url     : https://prove2.me/theorems/69938e3c-af23-41ec-8331-576caf166fd1
-- statement:
--   A Boolean assignment on a variable type V is a function V → Bool, and a literal (v,b) is true precisely when the assigned value of v equals b. Gate inputs are literals or Boolean constants; a raw clause is a finite list of gate inputs evaluated by disjunction. A depth-three circuit consists of finitely many bottom clauses, finitely many middle gates each conjoining a selected finite set of bottom gates, and one top gate disjoining a selected finite set of middle gates. Empty disjunctions are false and empty conjunctions are true. Its gate count is the number of bottom gates plus the number of middle gates plus one, including gates that are not connected to the output, and it computes a Boolean function when their values agree on every assignment. For a partial transition function S → Option S, runSteps iterates it a specified number of times, with failure remaining failure. A multitape configuration consists of a control state and a tape for each tape index. A transition reads all current head symbols and either halts or specifies a new state, a symbol to write on each tape, and a left, stationary, or right move for each head; writing precedes movement. A finite multitape machine has finite tape, alphabet, and state types, a distinguished input tape and initial state, an injective encoding of the two input bits as nonblank symbols, transition code, and a Boolean acceptance function on states. Initialization loads the encoded input onto the input tape and leaves other tapes blank. MultiTapeHaltsIn(M,input,output,time) means that, after some k ≤ time successful transitions from initialization, the machine is in a configuration with no next transition and whose state has acceptance value output.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DepthThree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DepthThree.lean; bytes 16..3941
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace DepthThreeLowerBound

universe uV uS uK uGamma uQ

abbrev Cube (V : Type uV) := V → Bool
abbrev Literal (V : Type uV) := V × Bool

variable {V : Type uV}

namespace Literal

def eval (l : Literal V) (x : Cube V) : Bool := decide (x l.1 = l.2)

end Literal

abbrev GateInput (V : Type uV) := Sum (Literal V) Bool
abbrev RawClause (V : Type uV) := List (GateInput V)

namespace GateInput

def eval : GateInput V → Cube V → Bool
  | .inl l, x => l.eval x
  | .inr b, _ => b

end GateInput

namespace RawClause

noncomputable def eval (C : RawClause V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ l ∈ C, l.eval x = true)

end RawClause

structure Circuit3 (V : Type uV) where
  bottomCount : ℕ
  middleCount : ℕ
  bottom : Fin bottomCount → RawClause V
  middle : Fin middleCount → Finset (Fin bottomCount)
  top : Finset (Fin middleCount)

namespace Circuit3

def gateCount (C : Circuit3 V) : ℕ := C.bottomCount + C.middleCount + 1

noncomputable def middleEval (C : Circuit3 V) (j : Fin C.middleCount)
    (x : Cube V) : Bool := by
  classical
  exact decide (∀ i ∈ C.middle j, (C.bottom i).eval x = true)

noncomputable def eval (C : Circuit3 V) (x : Cube V) : Bool := by
  classical
  exact decide (∃ j ∈ C.top, C.middleEval j x = true)

def Computes (C : Circuit3 V) (f : Cube V → Bool) : Prop := ∀ x, C.eval x = f x

end Circuit3

def runSteps {S : Type uS} (step : S → Option S) (n : ℕ) (c : Option S) : Option S :=
  (fun oc => oc.bind step)^[n] c

inductive HeadMove
  | left
  | stay
  | right

def HeadMove.apply {Γ : Type uGamma} [Inhabited Γ] : HeadMove → Turing.Tape Γ → Turing.Tape Γ
  | .left, t => t.move Turing.Dir.left
  | .stay, t => t
  | .right, t => t.move Turing.Dir.right

structure MultiTapeCfg (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) [Inhabited Γ] where
  q : Q
  tapes : K → Turing.Tape Γ

abbrev MultiTapeCode (K : Type uK) (Γ : Type uGamma) (Q : Type uQ) :=
  Q → (K → Γ) → Option (Q × (K → Γ) × (K → HeadMove))

def multiTapeUpdate {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ] (c : MultiTapeCfg K Γ Q)
    (q : Q) (writes : K → Γ) (moves : K → HeadMove) : MultiTapeCfg K Γ Q :=
  ⟨q, fun k => (moves k).apply ((c.tapes k).write (writes k))⟩

def multiTapeStep {K : Type uK} {Γ : Type uGamma} {Q : Type uQ} [Inhabited Γ] (code : MultiTapeCode K Γ Q)
    (c : MultiTapeCfg K Γ Q) : Option (MultiTapeCfg K Γ Q) :=
  (code c.q (fun k => (c.tapes k).head)).map fun out =>
    multiTapeUpdate c out.1 out.2.1 out.2.2

structure FiniteMultiTapeMachine where
  K : Type
  [tapeFinite : Fintype K]
  [tapeDecidableEq : DecidableEq K]
  inputTape : K
  Γ : Type
  [alphabetInhabited : Inhabited Γ]
  [alphabetFinite : Fintype Γ]
  Q : Type
  [stateFinite : Fintype Q]
  initialState : Q
  inputSymbol : Bool → Γ
  input_injective : Function.Injective inputSymbol
  input_ne_blank : ∀ b, inputSymbol b ≠ default
  code : MultiTapeCode K Γ Q
  accept : Q → Bool

attribute [instance] FiniteMultiTapeMachine.tapeFinite
  FiniteMultiTapeMachine.tapeDecidableEq FiniteMultiTapeMachine.alphabetInhabited
  FiniteMultiTapeMachine.alphabetFinite FiniteMultiTapeMachine.stateFinite

namespace FiniteMultiTapeMachine

abbrev Cfg (M : FiniteMultiTapeMachine) := MultiTapeCfg M.K M.Γ M.Q

abbrev step (M : FiniteMultiTapeMachine) : M.Cfg → Option M.Cfg :=
  multiTapeStep M.code

def init (M : FiniteMultiTapeMachine) (input : List Bool) : M.Cfg :=
  ⟨M.initialState, fun k =>
    if k = M.inputTape then Turing.Tape.mk₁ (input.map M.inputSymbol)
    else Turing.Tape.mk₁ []⟩

end FiniteMultiTapeMachine

def MultiTapeHaltsIn (M : FiniteMultiTapeMachine) (input : List Bool)
    (output : Bool) (time : ℕ) : Prop :=
  ∃ k ≤ time, ∃ c : M.Cfg,
    runSteps M.step k (some (M.init input)) = some c ∧
    M.step c = none ∧ M.accept c.q = output



end DepthThreeLowerBound
end OAI


