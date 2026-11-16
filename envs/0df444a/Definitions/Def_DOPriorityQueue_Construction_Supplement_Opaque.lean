-- Prove2me | Definitions.Def_DOPriorityQueue_Construction_Supplement_Opaque
-- name    : DOPriorityQueue_Construction_Supplement_Opaque
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:40:12.140277+00:00
-- url     : https://prove2.me/theorems/b3a599bb-4fac-4791-893e-0df40090ad6e
-- title:
--   §6.2 — causal opaque-token cell-probe executions
-- statement:
--   A machine has $M$ private word slots and a passive addressed server, with $w$-bit numeric words. A cell is vacant, numeric, or one whole opaque token. All persistent private information, including control state and retained answers, must be in those $M$ slots. Public initial numeric contents may be arbitrary; no input token is initially present.
--
--   The controller sees numeric values and occupancy, never token identities. Its arbitrary free local functions can create numeric words, select and copy resident cells, or discard them. The current insertion supplies its token exactly once. A server read brings the addressed cell into one private slot; a write copies a resident cell or writes numeric data. Each read or write produces one counted address/direction probe. An extraction can return a token only from a private slot. No rule constructs a token from its numeric identity or jointly encodes tokens. Future inputs and delivered previous outputs are unavailable.
--
--   Finite executions generate call-grouped traces and answers. Completed executions receive independent uniform-word cylinder masses. The correctness predicate requires exact stable queue answers, termination on every infinite random tape, and normalization on every admissible history. It assumes no entropy or cost bound. The induced trace kernel is the derived normalized execution law; its fallback off that domain is excluded in every theorem. The supported permutations of a fixed trace are taken over all actual possible finite executions, including prefixes of zero-probability infinite tapes.
--
--   This general controller interface permits arbitrary free computations on metadata instead of restricting queues to the published sixteen-register RAM. Atomic local and arrival maps also relax transient numeric workspace and permit free public numeric initialization; the lower bounds cover this larger class. Stored private words remain bounded by $M$, and tokens can enter only through arrivals and counted reads. This relaxation preserves the source's fixed-trace counting argument and includes every source machine.
-- source:
--   Zimai Guo, Cheng Hong, Zhechen Li, STOC 2027 submission #538 (October 2026), pp. 3, 27, 29–30, Section 2.1 and Lemma 6.3

import Definitions.Def_DOPriorityQueue_Construction_Supplement_Experiment
import Definitions.Def_DOPriorityQueue_Construction_Execution

set_option autoImplicit false

namespace DOPriorityQueue.Construction.Supplement

/-- An arbitrary M-slot private store. Every persistent word, including retained
answers and control information, must live here. The server is passive. -/
structure OpaqueState (w M : ℕ) where
  client : Fin M → Option (RAM.Cell w ℕ)
  server : BitVec w → Option (RAM.Cell w ℕ)

/-- The controller can see numeric data and occupancy, never token identities. -/
inductive SlotView (w : ℕ) where
  | vacant
  | numeric (x : BitVec w)
  | token

def viewCell {w : ℕ} : Option (RAM.Cell w ℕ) → SlotView w
  | none => .vacant
  | some (.word x) => .numeric x
  | some (.ball _) => .token

/-- Free local computation may produce any word, copy any resident cell, or
discard it. Only the on-demand arrival rule may mention the current input token. -/
inductive SlotExpression (w M : ℕ) where
  | vacant
  | numeric (x : BitVec w)
  | resident (i : Fin M)
  | arriving

def evalSlot {w M : ℕ} (client : Fin M → Option (RAM.Cell w ℕ)) (input : Option ℕ) :
    SlotExpression w M → Option (RAM.Cell w ℕ)
  | .vacant => none
  | .numeric x => some (.word x)
  | .resident i => client i
  | .arriving => input.map RAM.Cell.ball

inductive OpaqueAction (w M : ℕ) where
  | local (update : Fin M → SlotExpression w M)
  | read (address : BitVec w) (destination : Fin M)
      (afterRead : Fin M → SlotExpression w M)
  | write (address : BitVec w) (value : SlotExpression w M)
      (afterWrite : Fin M → SlotExpression w M)
  | inserted
  | empty
  | output (priority : ℕ) (source : Fin M)

/-- General cell-probe controller, not the finite instruction set or its sixteen
register convention. Functions of the entire numeric view permit arbitrary free
causal local computation. There is no hidden persistent controller state.
The atomic local/arrival functions relax intermediate numeric workspace; this
only enlarges the lower-bound domain. No callback can read server data for free. -/
structure OpaqueProgram (w M : ℕ) where
  initialClient : Fin M → Option (BitVec w)
  initialServer : BitVec w → Option (BitVec w)
  insertInput : ℕ → (Fin M → SlotView w) → (Fin M → SlotExpression w M)
  extractInput : (Fin M → SlotView w) → (Fin M → SlotExpression w M)
  action : (Fin M → SlotView w) → BitVec w → OpaqueAction w M

def opaqueInitial {w M : ℕ} (Q : OpaqueProgram w M) : OpaqueState w M :=
  ⟨fun i => (Q.initialClient i).map RAM.Cell.word,
    fun a => (Q.initialServer a).map RAM.Cell.word⟩

/-- The current operation is supplied once; future inputs and previous answers
are not accessible to the controller. Its payload arrives only at this event. -/
def opaqueEnter {w M : ℕ} (Q : OpaqueProgram w M) (s : OpaqueState w M) :
    Operation ℕ → OpaqueState w M
  | .insert p b =>
    { s with client := fun i =>
        evalSlot s.client (some b) (Q.insertInput p (fun j => viewCell (s.client j)) i) }
  | .extractMin =>
    { s with client := fun i =>
        evalSlot s.client none (Q.extractInput (fun j => viewCell (s.client j)) i) }

structure OpaqueCall (w M : ℕ) where
  state : OpaqueState w M
  remainingCoins : List (BitVec w)
  probes : List (RAM.Probe w)
  answer : Answer ℕ

/-- Each action receives a fresh uniform random word. Deterministic actions may
ignore it. Local transformations copy/discard resident tokens; no arithmetic or
numeric token identifier can manufacture a payload. All server accesses count. -/
def opaqueCall {w M : ℕ} (Q : OpaqueProgram w M) :
    ℕ → OpaqueState w M → List (BitVec w) → Option (OpaqueCall w M)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, s, coin :: coins => do
    let a := Q.action (fun i => viewCell (s.client i)) coin
    match a with
    | .local update =>
      opaqueCall Q fuel { s with client := fun i => evalSlot s.client none (update i) } coins
    | .read address destination update =>
      let loaded := Function.update s.client destination (s.server address)
      let r ← opaqueCall Q fuel
        { s with client := fun i => evalSlot loaded none (update i) } coins
      return { r with probes := ⟨address, false⟩ :: r.probes }
    | .write address value update =>
      let r ← opaqueCall Q fuel
        { client := fun i => evalSlot s.client none (update i)
          server := Function.update s.server address (evalSlot s.client none value) } coins
      return { r with probes := ⟨address, true⟩ :: r.probes }
    | .inserted => return ⟨s, coins, [], .inserted⟩
    | .empty => return ⟨s, coins, [], .extracted none⟩
    | .output priority source =>
      match s.client source with
      | some (.ball b) => return ⟨s, coins, [], .extracted (some (priority, b))⟩
      | _ => none

structure OpaqueRun (w M : ℕ) where
  state : OpaqueState w M
  remainingCoins : List (BitVec w)
  traces : RAM.Trace w
  answers : List (Answer ℕ)

def opaqueRun {w M : ℕ} (Q : OpaqueProgram w M) (fuel : ℕ) :
    OpaqueState w M → List (BitVec w) → List (Operation ℕ) → Option (OpaqueRun w M)
  | s, coins, [] => some ⟨s, coins, [], []⟩
  | s, coins, op :: h => do
    let r ← opaqueCall Q fuel (opaqueEnter Q s op) coins
    let rest ← opaqueRun Q fuel r.state r.remainingCoins h
    return ⟨rest.state, rest.remainingCoins, r.probes :: rest.traces, r.answer :: rest.answers⟩

noncomputable def opaqueCompleted {w M : ℕ} (Q : OpaqueProgram w M)
    (h : List (Operation ℕ)) (coins : List (BitVec w)) : Option (OpaqueRun w M) := by
  classical
  let returns := fun fuel => ∃ r,
    opaqueRun Q fuel (opaqueInitial Q) coins h = some r ∧ r.remainingCoins = []
  exact if ht : ∃ fuel, returns fuel then
    opaqueRun Q (Nat.find ht) (opaqueInitial Q) coins h else none

noncomputable def opaqueMass {w M : ℕ} (Q : OpaqueProgram w M)
    (h : List (Operation ℕ)) (v : RAM.Trace w) : ENNReal := by
  classical
  exact ∑' coins : List (BitVec w),
    match opaqueCompleted Q h coins with
    | none => 0
    | some r => if r.traces = v then RAM.coinPrefixMass w coins else 0

/-- Off the normalized domain the fallback is irrelevant. Every use requires
opaqueCorrect, which asserts normalization on each admissible history. -/
noncomputable def opaqueKernel {w M : ℕ} (Q : OpaqueProgram w M) : TraceKernel w := by
  classical
  exact fun h => if hn : HasSum (opaqueMass Q h) 1 then ⟨opaqueMass Q h, hn⟩ else PMF.pure []

/-- Only the source's exactness, every-tape termination and normalized law.
No entropy, probe, routing, or lower-bound guarantee is assumed. -/
def opaqueCorrect {w M : ℕ} (Q : OpaqueProgram w M) (T U : ℕ) : Prop :=
  ∀ h : List (Operation ℕ), validHistory T U h →
    (∀ tape : ℕ → BitVec w, ∃ k fuel r,
      opaqueRun Q fuel (opaqueInitial Q) (List.ofFn (fun i : Fin k => tape i.val)) h = some r ∧
        r.remainingCoins = []) ∧
    (∀ fuel coins r, opaqueRun Q fuel (opaqueInitial Q) coins h = some r →
      r.answers = exactAnswers h) ∧
    HasSum (opaqueMass Q h) 1

/-- Actual possible executions, not just positive-mass support. In particular
there is no probability cutoff that could discard measure-zero random tapes. -/
noncomputable def tracePermutations {n w M : ℕ} (Q : OpaqueProgram w M)
    (b : Fin n → ℕ) (v : RAM.Trace w) : Finset (List (Fin n)) := by
  classical
  exact ((List.finRange n).permutations.toFinset).filter fun π =>
    ∃ (X : Fin n → Fin n) (fuel : ℕ) (coins : List (BitVec w)) (r : OpaqueRun w M),
      opaqueRun Q fuel (opaqueInitial Q) coins (experimentHistory b X) = some r ∧
      r.traces = v ∧ stablePermutation X = π

end DOPriorityQueue.Construction.Supplement


