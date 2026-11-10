-- Prove2me | Definitions.Def_InteractionElim_Main_Machine
-- name    : InteractionElim_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:21:52.306393+00:00
-- url     : https://prove2.me/theorems/23dead18-a0cd-4247-bd48-5a1a7abec23e
-- title:
--   The bit-cost stack machine with private coins, the explicit binary input of bit length $N$, and the protocol and implementation time induced by one uniform program
-- statement:
--   A **program** is a finite list of instructions acting on stacks of bits (indexed by $0,1,2,\dots$): push a bit, pop, a three-way branch on the top of a stack (1 / 0 / empty), push the next bit of the private coin tape, halt. Each executed instruction is one step and touches $O(1)$ bits. The input is placed on stack $0$ and the output is stack $1$ at halting.
--
--   The **explicit binary input** of an instance lists $R$, $m$, the block of every coordinate, the matrix $A$ row by row, the rationals $p_i$, and $w,\gamma,\delta$ (numerator and denominator), in a fixed self-delimiting binary code; its length is $N$.
--
--   A single program $\mathrm{prog}$ **induces a protocol** on every instance: the parser's speaker and phase flag at $H$, the agent's action from $(u,\text{view})$ and its tape, and the expert's bit and abandonment decision from $(Ax,H)$ and its tape are each the decoded output of one halting run of $\mathrm{prog}$ on a role tag, the explicit input and that party's current view (non-halting runs give no speaker / abandonment). The **implementation time** of an execution path is the total number of machine steps of all decisions taken along it, including both parser speaker and phase computations; since every decision is recomputed from the explicit input, it includes construction (the geometric optimization) and decoding.
--
--   **Formalization Note** The tool calls, paid bits, submissions and abandonment of an implementation are the decoded decisions, executed by the protocol semantics of `Protocol`. Multi-stack machines and Turing machines simulate each other with polynomial overhead. `implTime` is in $[0,\infty]$ and is $\infty$ when some decision does not halt.
-- source:
--   Jin, Zang, Xu, Li, Eliminating Ongoing Interaction in Long-Running Verification Agents, STOC 2027 submission (manuscript sha256 44f6d829…), p. 6, §2 'explicit binary input' and Theorem 3.1; p. 95, Proposition N.2; pp. 47-48, §F.7

import Mathlib
import Definitions.Def_InteractionElim_Main_Protocol

open scoped BigOperators ENNReal
open MeasureTheory Matrix

namespace InteractionElim.Main

/-!
# The bit-cost machine, the explicit binary input, and uniform implementations

Source: Jin, Zang, Xu, Li, *Eliminating Ongoing Interaction in Long-Running Verification Agents*,
STOC 2027 submission (manuscript sha256 44f6d829…), p. 6 ("The explicit binary input lists the
blocks, A, and rational p_i, w, γ, δ. Its bit length is N. … Private computation and geometric
optimization are included in implementation time"), Theorem 3.1 (p. 6), Proposition N.2
(p. 95) and §F.7 (pp. 47–48).

**Machine.** A program is a finite list of instructions acting on finitely many stacks of bits
(indexed by `ℕ`), with a program counter and a private coin tape read sequentially. Every
executed instruction costs one step and touches `O(1)` bits: `push`, `pop`, a three-way branch
on the top bit of a stack (true / false / empty), `coin` (push the next private tape bit) and
`halt`; running off the program halts. The input is placed on stack `0` (first bit on top) and
the output is stack `1` at halting. Multi-stack machines and Turing machines simulate each other
with polynomial overhead.

**Uniform implementation.** One program `prog`, fixed before the instance, implements the
parser, the agent and the expert of a protocol: each decision is one halting run of `prog` on
a role tag, the explicit input of the instance, and the deciding party's current view (the
public history for the parser and the expert, with the expert's record `A x`; `u` and the whole
private view for the agent), reading the party's own private tape (the parser reads no coins).
Tool calls, paid bits, submissions and abandonment are the decoded outputs; their effects are
those of the protocol semantics. Every decision is recomputed from the explicit input, so the
implementation time (the total number of machine steps of all decisions along an execution
path) includes construction (geometric optimization) and decoding.
-/

/-- A machine instruction. -/
inductive Instr where
  /-- Push bit `b` on stack `s`. -/
  | push (s : ℕ) (b : Bool)
  /-- Pop stack `s` (no effect on an empty stack). -/
  | pop (s : ℕ)
  /-- Jump to `ifTrue`, `ifFalse` or `ifEmpty` according to the top of stack `s`. -/
  | branch (s : ℕ) (ifTrue ifFalse ifEmpty : ℕ)
  /-- Push the next private coin on stack `s`. -/
  | coin (s : ℕ)
  /-- Halt. -/
  | halt

/-- A program. -/
abbrev Program := List Instr

/-- A machine configuration. -/
structure MState where
  pc : ℕ
  stk : ℕ → List Bool
  cursor : ℕ
  halted : Bool

/-- One machine step with private tape `ρ`. -/
def mstep (prog : Program) (ρ : Tape) (s : MState) : MState :=
  if s.halted then s else
  match prog[s.pc]? with
  | none => { s with halted := true }
  | some (.push k b) =>
      { s with pc := s.pc + 1, stk := Function.update s.stk k (b :: s.stk k) }
  | some (.pop k) =>
      { s with pc := s.pc + 1, stk := Function.update s.stk k (s.stk k).tail }
  | some (.branch k t f e) =>
      { s with pc := match (s.stk k).head? with
                     | some true => t
                     | some false => f
                     | none => e }
  | some (.coin k) =>
      { s with pc := s.pc + 1, stk := Function.update s.stk k (ρ s.cursor :: s.stk k),
               cursor := s.cursor + 1 }
  | some .halt => { s with halted := true }

/-- The configuration after `t` steps on input `inp`. -/
def mrun (prog : Program) (inp : List Bool) (ρ : Tape) (t : ℕ) : MState :=
  (mstep prog ρ)^[t]
    { pc := 0, stk := fun k => if k = 0 then inp else [], cursor := 0, halted := false }

open Classical in
/-- The output (stack `1` at halting), if the run halts. -/
noncomputable def progOut (prog : Program) (inp : List Bool) (ρ : Tape) : Option (List Bool) :=
  if h : ∃ t, (mrun prog inp ρ t).halted = true then
    some ((mrun prog inp ρ (Nat.find h)).stk 1)
  else none

open Classical in
/-- The number of steps until halting (`∞` if the run does not halt). -/
noncomputable def progTime (prog : Program) (inp : List Bool) (ρ : Tape) : ℝ≥0∞ :=
  if h : ∃ t, (mrun prog inp ρ t).halted = true then (Nat.find h : ℝ≥0∞) else ⊤

/-! ## Explicit binary encodings -/

/-- A natural number: each binary digit (least significant first) preceded by `1`, then `0`. -/
def encNat (n : ℕ) : List Bool := (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- An integer: sign bit, then the absolute value. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- A rational: numerator and (positive) denominator in lowest terms. -/
def encRat (q : ℚ) : List Bool := encInt q.num ++ encNat q.den

/-- A list: each item preceded by `1`, then `0`. -/
def encList {α : Type*} (f : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (fun a => true :: f a) ++ [false]

/-- A bit of `F_2`. -/
def encBit (b : ZMod 2) : List Bool := [decide (b = 1)]

/-- A vector of `F_2^n`. -/
def encVec {n : ℕ} (v : Fin n → ZMod 2) : List Bool := encList encBit (List.ofFn v)

/-- The explicit binary input of §2: `R`, `m`, the block of every coordinate, the matrix `A`
(row by row), the rationals `p_i`, and `w`, `γ`, `δ`. -/
def encInstance (I : Instance) : List Bool :=
  encNat I.R ++ encNat I.m ++ encList encNat (List.ofFn fun i => (I.block i : ℕ)) ++
    encNat I.nrows ++ encList encVec (List.ofFn fun a => I.A a) ++
    encList encRat (List.ofFn I.p) ++ encRat I.w ++ encRat I.γ ++ encRat I.δ

/-- The bit length `N` of the explicit input. -/
def Instance.N (I : Instance) : ℕ := (encInstance I).length

/-- A public event. -/
def encEvent {R : ℕ} : Event R → List Bool
  | .bit b => [false, b]
  | .submit v ub => true :: (encVec v ++ encBit ub)

/-- A public history. -/
def encHist {R : ℕ} (H : History R) : List Bool := encList encEvent H

/-- An entry of the agent's view. -/
def encObs {R : ℕ} : AgentObs R → List Bool
  | .pub e => false :: encEvent e
  | .obs i r => true :: (encNat i ++ encBit r)

/-- An agent action. -/
def encAct {R : ℕ} : AgentAct R → List Bool
  | .query i => encNat 0 ++ encNat i
  | .bit b => encNat 1 ++ [b]
  | .submit v ub => encNat 2 ++ encVec v ++ encBit ub
  | .yield => encNat 3
  | .abandon => encNat 4

/-! ## The protocol induced by a program -/

/-- The all-`false` tape (the parser uses no coins). -/
def zeroTape : Tape := fun _ => false

/-- Parser input: role tag `0` (speaker) or `1` (phase flag), instance, history. -/
def parserInput (I : Instance) (tag : ℕ) (H : History I.R) : List Bool :=
  encNat tag ++ encInstance I ++ encHist H

/-- Agent input: role tag `2`, instance, `u`, the agent's view. -/
def agentInput (I : Instance) (u : ZMod 2) (l : List (AgentObs I.R)) : List Bool :=
  encNat 2 ++ encInstance I ++ encBit u ++ encList encObs l

/-- Expert input: role tag `3` (paid bit) or `4` (abandonment), instance, record, history. -/
def expertInput (I : Instance) (tag : ℕ) (y : Fin I.nrows → ZMod 2) (H : History I.R) :
    List Bool :=
  encNat tag ++ encInstance I ++ encVec y ++ encHist H

/-- Decoding a speaker: `[false]` = agent, `[true]` = expert, anything else (or no halt) = none. -/
def decSpeaker : Option (List Bool) → Option Party
  | some [false] => some .agent
  | some [true] => some .expert
  | _ => none

/-- Decoding a flag: `[true]` = true, `[false]` = false, otherwise the default. -/
def decFlag (dflt : Bool) : Option (List Bool) → Bool
  | some [true] => true
  | some [false] => false
  | _ => dflt

open Classical in
/-- Decoding an agent action (`encAct` is injective); anything else (or no halt) = abandon. -/
noncomputable def decAct {R : ℕ} : Option (List Bool) → AgentAct R
  | some l => if h : ∃ a : AgentAct R, encAct a = l then Classical.choose h else .abandon
  | none => .abandon

/-- The protocol that the program `prog` induces on the instance `I`. A run that does not halt
yields: no speaker, phase off, agent abandonment, expert bit `0`, expert abandonment. -/
noncomputable def inducedProtocol (prog : Program) (I : Instance) : Protocol I where
  parser :=
    { speaker := fun H => decSpeaker (progOut prog (parserInput I 0 H) zeroTape)
      phase := fun H => decFlag false (progOut prog (parserInput I 1 H) zeroTape) }
  agent := fun ρ u l => decAct (progOut prog (agentInput I u l) ρ)
  expertBit := fun ρ y H => decFlag false (progOut prog (expertInput I 3 y H) ρ)
  expertAbandon := fun ρ y H => decFlag true (progOut prog (expertInput I 4 y H) ρ)

open Classical in
/-- The machine steps charged to one execution step from state `st` (zero once the run has
stopped): the parser's speaker and phase computations, the agent's decision, the expert's bit if the
agent yields, and the expert's abandonment decision at a newly reached public history. -/
noncomputable def stepWork (prog : Program) (I : Instance) (x : Fin I.R → ZMod 2) (u : ZMod 2)
    (ω : Ω I.R) (st : State I.R) : ℝ≥0∞ :=
  if st.status ≠ .running then 0 else
    progTime prog (parserInput I 0 st.hist) zeroTape +
    progTime prog (parserInput I 1 st.hist) zeroTape +
    progTime prog (agentInput I u st.log) (agentTape ω) +
    (if (inducedProtocol prog I).agent (agentTape ω) u st.log = .yield then
        progTime prog (expertInput I 3 (I.A *ᵥ x) st.hist) (expertTape ω) else 0) +
    (if (step (inducedProtocol prog I) x u ω st).hist.length ≠ st.hist.length then
        progTime prog (expertInput I 4 (I.A *ᵥ x) (step (inducedProtocol prog I) x u ω st).hist)
          (expertTape ω) else 0)

/-- The implementation time of the execution path `ω` in world `(x, u)`: all machine steps of
all decisions (the expert's abandonment check at the empty history included). -/
noncomputable def implTime (prog : Program) (I : Instance) (x : Fin I.R → ZMod 2) (u : ZMod 2)
    (ω : Ω I.R) : ℝ≥0∞ :=
  progTime prog (expertInput I 4 (I.A *ᵥ x) []) (expertTape ω) +
    ∑' t, stepWork prog I x u ω (run (inducedProtocol prog I) x u ω t)

/-- The total number of tool calls made by step `t`. -/
def State.totalCalls {R : ℕ} (st : State R) : ℕ := ∑ i, st.calls i

end InteractionElim.Main


