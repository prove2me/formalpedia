-- Prove2me | Definitions.Def_CNFLearnMQ_Supplement_SampleMachine
-- name    : CNFLearnMQ_Supplement_SampleMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:03:07.759198+00:00
-- url     : https://prove2.me/theorems/dbca89a2-fcbc-4911-bc99-6eff87e21997
-- title:
--   Randomized multi-stack machines with a sample oracle, their running time and output hypotheses
-- statement:
--   This is the cost model for the hardness results of §7. A **sample machine** has a finite set of control states, a finite stack alphabet and finitely many stacks. In each step it reads the top symbol of every stack and does one of four things: it halts; it makes a local move (changes state and, on each stack, keeps, pops, or pushes one symbol); it flips a fair coin; or it asks the sample oracle, which pushes one fresh independent sample, written as a self-delimited bit string, onto a designated sample stack. Every non-halting step costs one unit of time. The input parameters (natural numbers in binary) start on an input stack.
--
--   When the learning run halts, its final configuration stores the **output hypothesis**: to evaluate it on $x\in\{0,1\}^n$, $x$ is written onto the input stack and the machine restarts, deterministically, in a designated evaluation state, and the answer is read off the halting state. A machine **runs within time $b$** if, on every outcome of positive probability, the learning run halts within $b$ steps and the stored hypothesis answers every $x\in\{0,1\}^n$ within $b$ further steps. This implements "running time includes evaluating the output hypothesis on any input" (p.5).
--
--   **Formalization Note** Bounding the learning run and every evaluation by the same $b$ differs from bounding their sum by at most a factor $2$, which the $O_r(\cdot)$ constants absorb. The oracle writes a sample in one step, as an oracle tape does; reading it costs one step per symbol. An evaluation that flips a coin, asks for a sample or exceeds its budget gives no answer (and reads as $0$).
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Hypotheses 1.5–1.6, p.5 ("running time includes evaluating the output hypothesis on any input"); Theorem 7.1, pp.40–41

import Mathlib

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

/-!
# Randomized multi-stack machines with a sample oracle

The cost model of §7 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and
Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…), Hypotheses 1.5–1.6,
p.5, and Theorem 7.1, pp.40–41): a "randomized algorithm" with "only i.i.d. samples", its running
time, and the evaluation of the hypothesis it outputs ("running time includes evaluating the output
hypothesis on any input", p.5).

A machine has a finite set of control states, a finite stack alphabet and finitely many stacks.
Each step reads the top symbol of every stack and either halts, performs one local move (new state;
on each stack keep, pop, or push one symbol), flips one fair coin, or asks the sample oracle, which
pushes one fresh independent sample (written self-delimited) onto the designated sample stack. Every
non-halting step costs one unit of time; no computation is free.
-/

/-- An operation on one stack. -/
inductive StackOp (Γ : Type) where
  | keep : StackOp Γ
  | pop : StackOp Γ
  | push : Γ → StackOp Γ

/-- One action of a machine. -/
inductive Act (Q K Γ : Type) where
  /-- Stop. -/
  | halt : Act Q K Γ
  /-- Go to state `q` and apply `ops k` to every stack `k`. -/
  | move : Q → (K → StackOp Γ) → Act Q K Γ
  /-- Flip a fair coin: go to `q₀` on `false`, `q₁` on `true`. -/
  | coin : Q → Q → Act Q K Γ
  /-- Ask for one fresh sample, pushed onto the sample stack; go to `q`. -/
  | sample : Q → Act Q K Γ

/-- A randomized multi-stack machine with a sample oracle. The input parameters are written on the
stack `inK`; samples arrive on `sampleK`; a bit `b` is written as the symbol `bit b`. Learning starts
in `start`. To evaluate the output hypothesis on `x`, the point `x` is written on `inK` on top of the
stacks left by the learning run and the machine restarts in `evalStart`; it answers `accept q` in the
state `q` where it halts. -/
structure SampleMachine where
  /-- Control states. -/
  Q : Type
  [qFin : Fintype Q]
  /-- Stack alphabet. -/
  Γ : Type
  [γFin : Fintype Γ]
  /-- Stack names. -/
  K : Type
  [kFin : Fintype K]
  [kDec : DecidableEq K]
  /-- The input stack. -/
  inK : K
  /-- The sample stack. -/
  sampleK : K
  /-- How a bit is written. -/
  bit : Bool → Γ
  /-- Initial state of the learning run. -/
  start : Q
  /-- Initial state of an evaluation of the output hypothesis. -/
  evalStart : Q
  /-- The transition function: the action taken in a state, given the top symbol of every stack. -/
  next : Q → (K → Option Γ) → Act Q K Γ
  /-- The answer of an evaluation that halts in a given state. -/
  accept : Q → Bool

attribute [instance] SampleMachine.qFin SampleMachine.γFin SampleMachine.kFin SampleMachine.kDec

namespace SampleMachine

variable (M : SampleMachine)

/-- A configuration: control state and stack contents (head of a list = top of the stack). -/
structure Cfg (M : SampleMachine) : Type where
  /-- The control state. -/
  state : M.Q
  /-- The stack contents. -/
  stk : M.K → List M.Γ

/-- Apply a stack operation. -/
def applyOp {Γ : Type} : StackOp Γ → List Γ → List Γ
  | .keep, l => l
  | .pop, l => l.tail
  | .push g, l => g :: l

/-- Self-delimited writing of a bit string: each bit `b` becomes `true, b`; the string ends with
`false, false`. -/
def encBits (u : List Bool) : List Bool := u.flatMap (fun b => [true, b]) ++ [false, false]

/-- A list of natural numbers, each written in binary (least significant bit first, Mathlib's
`Nat.bits`), self-delimited. -/
def encNats (l : List ℕ) : List Bool := l.flatMap fun m => encBits (Nat.bits m)

/-- Push the self-delimited writing of `u` onto a stack (first bit on top). -/
def pushBits (u : List Bool) (l : List M.Γ) : List M.Γ := (encBits u).map M.bit ++ l

/-- The top symbols of all stacks. -/
def tops (c : M.Cfg) : M.K → Option M.Γ := fun k => (c.stk k).head?

/-- The initial configuration on the parameters `params`: state `start`, the parameters written on
the input stack, every other stack empty. -/
def initCfg (params : List ℕ) : M.Cfg :=
  ⟨M.start, fun k => if k = M.inK then (encNats params).map M.bit else []⟩

/-- The learning run with time budget `b`, sample law `μ` (a law on bit strings) and fair coins:
the law of the halting configuration, or `none` if the machine has not halted after `b` steps.
Every non-halting step (a move, a coin flip, a sample request) costs one unit. -/
noncomputable def runFor (μ : PMF (List Bool)) : ℕ → M.Cfg → PMF (Option M.Cfg)
  | b, c =>
    match M.next c.state (M.tops c), b with
    | .halt, _ => PMF.pure (some c)
    | _, 0 => PMF.pure none
    | .move q ops, b + 1 => runFor μ b ⟨q, fun k => applyOp (ops k) (c.stk k)⟩
    | .coin q₀ q₁, b + 1 => (PMF.uniformOfFintype Bool).bind fun β =>
        runFor μ b ⟨if β then q₁ else q₀, c.stk⟩
    | .sample q, b + 1 => μ.bind fun u =>
        runFor μ b ⟨q, Function.update c.stk M.sampleK (M.pushBits u (c.stk M.sampleK))⟩

/-- A deterministic evaluation with time budget `b`: `some (accept q)` if the machine halts in
state `q` within `b` steps, `none` if it does not halt in time or uses a coin or the sample oracle
(an output hypothesis must be a deterministic function). -/
def evalFor : ℕ → M.Cfg → Option Bool
  | b, c =>
    match M.next c.state (M.tops c), b with
    | .halt, _ => some (M.accept c.state)
    | _, 0 => none
    | .move q ops, b + 1 => evalFor b ⟨q, fun k => applyOp (ops k) (c.stk k)⟩
    | .coin _ _, _ + 1 => none
    | .sample _, _ + 1 => none

/-- The evaluation of the hypothesis stored in the halting configuration `c` on the point `x`, with
budget `b`: `x` is written on the input stack (on top of its remaining contents) and the machine
restarts in `evalStart`. -/
def evalAt (b : ℕ) (c : M.Cfg) (x : List Bool) : Option Bool :=
  M.evalFor b ⟨M.evalStart, Function.update c.stk M.inK (M.pushBits x (c.stk M.inK))⟩

/-- The Boolean function `{0,1}^n → {0,1}` output by a learning run ending in `c`, evaluated with
budget `b` (an evaluation that does not answer within the budget reads as `0`). -/
def hypothesis (b : ℕ) (c : M.Cfg) {n : ℕ} (x : Fin n → Bool) : Bool :=
  (M.evalAt b c (List.ofFn x)).getD false

/-- The machine runs within time `b` on the parameters `params` under the sample law `μ`, including
the evaluation of its output on any point of `{0,1}^n`: every outcome of positive probability halts
within `b` steps, and the hypothesis it stores answers every `x ∈ {0,1}^n` within `b` further steps.

**Formalization Note** The paper bounds "running time including evaluating the output on any
input" by one function; bounding the learning run and every evaluation by the same `b` differs from
bounding their sum by at most a factor `2`, which is absorbed by the `O_r(·)` constants. The bound
is worst case: on every outcome of positive probability. -/
def RunsWithin (μ : PMF (List Bool)) (params : List ℕ) (n b : ℕ) : Prop :=
  ∀ o ∈ (M.runFor μ b (M.initCfg params)).support,
    ∃ c, o = some c ∧ ∀ x : Fin n → Bool, (M.evalAt b c (List.ofFn x)).isSome

end SampleMachine

end CNFLearnMQ.Supplement


