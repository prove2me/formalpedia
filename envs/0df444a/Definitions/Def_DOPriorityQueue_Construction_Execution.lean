-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Execution
-- name    : DOPriorityQueue_Construction_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:03:19.988538+00:00
-- url     : https://prove2.me/theorems/dd18b5fc-a390-4685-a2eb-76e8f6428ca9
-- title:
--   §2 — online calls, every-tape termination and trace probabilities
-- statement:
--   The online driver exposes only the current operation to a program, retains its private and server state, and starts the next call at the fixed entry. Its mathematical result records answers and one probe list for each call, including empty lists; old answers are not retained in machine memory. Three input-register loads and one output delivery are charged per call.
--
--   A consumed finite prefix of $n$ independent $w$-bit random words has mass
--   $$2^{-wn}.$$
--   Completed runs consume exactly their supplied prefix. Trace-event probabilities and expected work are sums of these nonnegative cylinder masses, with work weighted by its executed instruction count. Every-tape termination requires a finite completed prefix on each infinite random-word tape, including tapes of probability zero. Exactness compares every completed execution with the stable queue specification.
--
--   Differential obliviousness quantifies over every admissible neighboring pair and every event of call-grouped traces:
--   $$\Pr[\operatorname{Access}(h)\in S]\le e^\varepsilon\Pr[\operatorname{Access}(h')\in S]+\delta.$$
--   All trace subsets are measurable in the discrete observation space. Normalization is required in the headline contract, so a zero law cannot satisfy it. No Boolean flag from an implementation is used as a privacy or termination certificate.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), pp. 3–4, §§2.1–2.2; pp. 36–37, Appendix B

import Definitions.Def_DOPriorityQueue_Construction_Queue
import Definitions.Def_DOPriorityQueue_Construction_RAM

set_option autoImplicit false

namespace DOPriorityQueue.Construction
namespace RAM

/-- Only public T and U are supplied before calls. No future operation is resident. -/
def initialState (w T U : ℕ) (Ball : Type) : State w Ball :=
  { pc := 0
    registers := fun r => .word (BitVec.ofNat w (if r = 3 then T else if r = 4 then U else 0))
    privateMemory := fun _ => none
    serverMemory := fun _ => none }

/-- Calling convention: 0 is code, 1 priority, 2 opaque input payload.
Other registers and both memories persist. Entry always starts at PC zero. -/
def enter {w : ℕ} {Ball : Type} (s : State w Ball) : Operation Ball → State w Ball
  | .insert p v =>
    putRegister (putRegister (putRegister { s with pc := 0 }
      0 (.word 0)) 1 (.word (BitVec.ofNat w p))) 2 (.ball v)
  | .extractMin =>
    putRegister (putRegister (putRegister { s with pc := 0 }
      0 (.word 1)) 1 (.word 0)) 2 (.word 0)

/-- Return code 0 acknowledges insertion; 1 reports empty extraction;
2 returns the priority in register 1 and whole opaque ball in register 2. -/
def decodeAnswer {w : ℕ} {Ball : Type} (s : State w Ball) : Option (Answer Ball) := do
  let code ← getWord s 0
  if code.toNat = 0 then return .inserted
  else if code.toNat = 1 then return .extracted none
  else if code.toNat = 2 then
    let p ← getWord s 1
    match s.registers 2 with
    | .ball v => return .extracted (some (p.toNat, v))
    | .word _ => none
  else none

structure HistoryResult (w : ℕ) (Ball : Type) where
  state : State w Ball
  remainingCoins : List (BitVec w)
  traces : Trace w
  answers : List (Answer Ball)
  work : ℕ
  peakPrivate : ℕ
  peakServer : ℕ

/-- The driver can supply only the current operation. It retains no old answers
in the machine. The result's answer list and metrics are semantic observations.
Three input loads and one output delivery are charged per external call. -/
def runHistory {w : ℕ} {Ball : Type} (program : List Instruction) (fuel : ℕ) :
    State w Ball → List (BitVec w) → List (Operation Ball) → Option (HistoryResult w Ball)
  | s, coins, [] => some ⟨s, coins, [], [], 0, privateWords s, serverWords s⟩
  | s, coins, op :: history => do
    let call ← runCall program fuel (enter s op) coins
    let answer ← decodeAnswer call.state
    let rest ← runHistory program fuel call.state call.remainingCoins history
    return ⟨rest.state, rest.remainingCoins, call.probes :: rest.traces,
      answer :: rest.answers, 4 + call.work + rest.work,
      max (privateWords s) (max call.peakPrivate rest.peakPrivate),
      max (serverWords s) (max call.peakServer rest.peakServer)⟩

/-- A finite coin prefix is terminal precisely when all of it is consumed by
this history. Choosing the least fuel prevents counting padding interpreter steps. -/
noncomputable def completedRun {w : ℕ} {Ball : Type} (program : List Instruction)
    (T U : ℕ) (history : List (Operation Ball)) (coins : List (BitVec w)) :
    Option (HistoryResult w Ball) := by
  classical
  let terminates := fun fuel => ∃ r,
    runHistory program fuel (initialState w T U Ball) coins history = some r ∧
      r.remainingCoins = []
  exact if h : ∃ fuel, terminates fuel then
    runHistory program (Nat.find h) (initialState w T U Ball) coins history
  else none

/-- Probability is a sum of actual random-word cylinder masses. It is not a
Bochner integral with a zero default on non-integrable running time. -/
noncomputable def traceProbability {w : ℕ} {Ball : Type} (program : List Instruction)
    (T U : ℕ) (history : List (Operation Ball)) (event : Set (Trace w)) : ENNReal := by
  classical
  exact ∑' coins : List (BitVec w),
    match completedRun program T U history coins with
    | none => 0
    | some r => if r.traces ∈ event then coinPrefixMass w coins else 0

noncomputable def expectedWork {w : ℕ} {Ball : Type} (program : List Instruction)
    (T U : ℕ) (history : List (Operation Ball)) : ENNReal :=
  ∑' coins : List (BitVec w),
    match completedRun program T U history coins with
    | none => 0
    | some r => coinPrefixMass w coins * (r.work : ENNReal)

/-- Termination holds on every infinite random-word tape, including measure-zero
tapes. An empty history consumes no words and takes no executed work. -/
def totalOnHistory {w : ℕ} {Ball : Type} (program : List Instruction)
    (T U : ℕ) (history : List (Operation Ball)) : Prop :=
  ∀ tape : ℕ → BitVec w, ∃ n fuel r,
    runHistory program fuel (initialState w T U Ball)
      (List.ofFn (fun i : Fin n => tape i.val)) history = some r ∧ r.remainingCoins = []

def exactOnHistory {w : ℕ} {Ball : Type} (program : List Instruction)
    (T U : ℕ) (history : List (Operation Ball)) : Prop :=
  totalOnHistory (w := w) program T U history ∧
    ∀ fuel coins r,
      runHistory program fuel (initialState w T U Ball) coins history = some r →
        r.answers = exactAnswers history

/-- Full-operation adjacency, arbitrary events of call-grouped finite traces. -/
noncomputable def isDO (w T U : ℕ) (program : List Instruction) (ε δ : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ δ ≤ 1 ∧
    ∀ (Ball : Type) (h h' : List (Operation Ball)),
      validHistory T U h → validHistory T U h' → neighbors h h' →
      ∀ event : Set (Trace w),
        traceProbability program T U h event ≤
          ENNReal.ofReal (Real.exp ε) * traceProbability program T U h' event +
            ENNReal.ofReal δ

end RAM
end DOPriorityQueue.Construction


