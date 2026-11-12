-- Prove2me | Definitions.Def_QuantumBA_PackedShares_Model
-- name    : QuantumBA_PackedShares_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:53.381423+00:00
-- url     : https://prove2.me/theorems/a959afa1-7155-4552-81f8-3ea3f8804ad7
-- title:
--   The synchronous quantum network model of §1.1: registers, adversary, execution law, agreement, validity, termination, costs
-- statement:
--   There are $n$ processes $P=[n]$ with input bits, classical memory and quantum registers; every pair is joined by reliable authenticated classical and quantum channels; rounds are synchronous and messages arrive at the end of the sending round. A register holding one element of $F=\mathbb F_q$ is a $q$-level system ($d$ qubits when $q=2^d$).
--
--   **States.** Registers are named by natural numbers; registers never allocated are in $|0\rangle$. The unnormalized joint state is a matrix indexed by computational-basis labels of all registers.
--
--   **Honest processes.** A protocol specifies local classical states and, per round, the operations of an honest non-halted process on its own registers (operators on listed registers, with fresh $|0\rangle$ registers), the registers it measures in the computational basis, and, after seeing the allocated register names and outcomes, its new state and the classical and quantum messages it sends; at the end of the round it receives the delivered messages.
--
--   **Adversary.** Computationally unbounded and full-information: every choice is a function of the whole classical history (all outcomes of all measurements and instruments). In every adversarial micro-step it applies a quantum instrument to registers it holds (its own memory, which it may enlarge by claiming fresh registers, and the registers of corrupted processes, including staged outgoing registers of a sender corrupted in the current round), then may corrupt one more process, never more than $t$ in total. Each round is: $n+1$ adversarial micro-steps; the honest step; $n+1$ adversarial micro-steps seeing all staged messages (rushing); delivery. At delivery, staged messages of senders still honest are delivered unchanged; messages of senders corrupted during the round are suppressed (the adversary holds their registers); the adversary sends any messages in the names of corrupted processes, quantum ones made of registers it holds.
--
--   **Law and properties.** The outcome of each micro-step has the Born-rule law given the history; the law of an infinite execution is the Ionescu–Tulcea measure. An *execution* is an outcome sequence all of whose finite prefixes have positive probability; a process is *correct* if it is never corrupted. **Agreement**: on every execution, correct processes never decide different bits. **Validity**: on every execution, if all correct inputs equal $v$, every decision of a correct process is $v$. **Termination**: with probability $1$ every correct process decides and halts. **Costs**: $R$ is the number of rounds through the last halt of a correct process; $Q$ and $C$ are the qubits and classical bits of all transmissions staged by honest processes in those rounds, each channel use costing at least one unit, a register costing $\log_2 q$ qubits.
--
--   **Formalization Note** Expectations are lower Lebesgue integrals of $[0,\infty]$-valued costs; transmissions are charged when staged, also if the sender is corrupted later in the round.
-- source:
--   Jan Olkowski, Fast Quantum Byzantine Agreement with Nearly Linear Quantum Communication, STOC 2027 submission #558 (October 2026), source.pdf SHA-256 612d0471810a0aa053891a77995d579d836cc301efd01df8e75c2bbe8ebb5383, pp. 1–2, §1.1 (PDF pp. 2–3); §3.3 histories (p. 14, PDF 15); Appendix A (p. 36, PDF 37)

import Mathlib

set_option autoImplicit false

open scoped BigOperators ENNReal Matrix

namespace QuantumBA.PackedShares

/-! # The synchronous quantum network model of §1.1

Registers are `F`-valued qudits named by natural numbers (a register holding one element of
`F = 𝔽_q` is `d` qubits).  A computational-basis label of the whole system is a function
`ℕ → F`; registers that have never been allocated are in `|0⟩`, so allocating a fresh register in
`|0⟩` does not change the state.  An unnormalized state is a kernel `(ℕ → F) → (ℕ → F) → ℂ`
(a density matrix in the computational basis). -/

/-- Unnormalized joint state of all registers, as a matrix indexed by computational-basis labels. -/
abbrev QState (F : Type) := (ℕ → F) → (ℕ → F) → ℂ

section Registers

variable {F : Type} [Zero F]

/-- Restriction of a basis label to registers named by `reg : ι → ℕ`. -/
def restrictF {ι : Type} (reg : ι → ℕ) (x : ℕ → F) : ι → F := fun i => x (reg i)

/-- Overwrite the registers named by an injective `reg : ι → ℕ` in the basis label `x` by `a`. -/
noncomputable def updateF {ι : Type} (reg : ι → ℕ) (x : ℕ → F) (a : ι → F) : ℕ → F := by
  classical
  exact fun j => if h : ∃ i, reg i = j then a h.choose else x j

variable [Fintype F] [DecidableEq F]

/-- `ρ ↦ (K ⊗ I) ρ (K ⊗ I)†`, where `K` acts on the registers named by the injective map
`reg : ι → ℕ` and the identity acts on all other registers. -/
noncomputable def applyKraus {ι : Type} [Fintype ι] [DecidableEq ι] (reg : ι → ℕ)
    (K : Matrix (ι → F) (ι → F) ℂ) (ρ : QState F) : QState F :=
  fun x y => ∑ a, ∑ b, K (restrictF reg x) a * ρ (updateF reg x a) (updateF reg y b) *
    star (K (restrictF reg y) b)

/-- Extension by `|0⟩` of a label on the first `m` registers. -/
def extN (m : ℕ) (a : Fin m → F) : ℕ → F := fun j => if h : j < m then a ⟨j, h⟩ else 0

/-- Trace of a state all of whose registers outside `0, …, m-1` are in `|0⟩`. -/
noncomputable def traceN (m : ℕ) (ρ : QState F) : ℂ := ∑ a : Fin m → F, ρ (extN m a) (extN m a)

/-- The initial state: every register in `|0⟩`. -/
noncomputable def initState : QState F := by
  classical
  exact fun x y => if x = 0 ∧ y = 0 then 1 else 0

/-- Projector of a computational-basis measurement of the registers `regs` (in list order) with
outcome list `vals`; it is zero if `vals` has the wrong length. -/
noncomputable def measProj (regs : List ℕ) (vals : List F) :
    Matrix (Fin regs.length → F) (Fin regs.length → F) ℂ := by
  classical
  exact fun a b => if a = b ∧ vals.length = regs.length ∧ ∀ i, a i = vals.getD i.1 0 then 1 else 0

end Registers

/-! ## Operations of honest processes and of the adversary -/

/-- A local operation of an honest process: a list of slots, each an existing register
(`some r`) or a freshly allocated register in `|0⟩` (`none`), and an operator `M` on the slots
(applied as `ρ ↦ M ρ M†`).  The protocol uses it only for operators that are isometric on the
states it applies them to (share encoders acting on inputs and fresh `|0⟩` ancillas). -/
structure HOp (F : Type) [Fintype F] where
  slots : List (Option ℕ)
  op : Matrix (Fin slots.length → F) (Fin slots.length → F) ℂ

/-- One adversarial quantum instrument in Kraus form, on a duplicate-free list of registers,
with outcomes `0, …, k-1`: `∑ᵢ Kᵢ† Kᵢ = 1`.  A general instrument (several Kraus operators per
outcome, arbitrary finite-dimensional memory) is obtained by first claiming fresh registers as
ancillas, so one Kraus operator per outcome loses no generality. -/
structure AdvInstr (F : Type) [Fintype F] [DecidableEq F] where
  regs : List ℕ
  nodup : regs.Nodup
  k : ℕ
  K : Fin k → Matrix (Fin regs.length → F) (Fin regs.length → F) ℂ
  complete : ∑ i, (K i)ᴴ * K i = 1

/-- The trivial instrument (one outcome, identity on no registers). -/
def AdvInstr.trivial (F : Type) [Fintype F] [DecidableEq F] : AdvInstr F where
  regs := []
  nodup := List.nodup_nil
  k := 1
  K := fun _ => 1
  complete := by simp

/-- A classical outcome of one micro-step: `tick` for deterministic steps, `adv i` for the
outcome of an adversarial instrument, `meas v` for the list of outcomes of the honest
computational-basis measurements of a round. -/
inductive Outcome (F : Type) where
  | tick : Outcome F
  | adv : ℕ → Outcome F
  | meas : List F → Outcome F

instance (F : Type) [Countable F] : Countable (Outcome F) := by
  classical
  have : Function.Injective (fun o : Outcome F => match o with
      | .tick => (Sum.inl () : Unit ⊕ (ℕ ⊕ List F))
      | .adv i => Sum.inr (Sum.inl i)
      | .meas v => Sum.inr (Sum.inr v)) := by
    intro a b h; cases a <;> cases b <;> simp_all
  exact this.countable

instance (F : Type) : MeasurableSpace (Outcome F) := ⊤

instance (F : Type) : DiscreteMeasurableSpace (Outcome F) := ⟨fun _ => trivial⟩

/-- A classical history: the list of micro-step outcomes so far.  Every classical datum of the
execution (states, messages, corruption choices, instrument outcomes) is a deterministic
function of the input vector, the adversary and this list. -/
abbrev History (F : Type) := List (Outcome F)

/-- A protocol for `n` processes: local classical states, classical message type `M` with its
bit length, per-register classical headers `Hd` of quantum messages with their bit length, and
the round behaviour of an honest process.  In each round an honest, non-halted process applies
`ops`, measures the registers `meas` in the computational basis (only registers it owns), and
then (knowing the ids of the registers it allocated and the measured register/outcome pairs) updates its state and stages classical messages
and quantum messages (lists of header/register pairs).  At the end of the round it receives the
delivered messages through `recv`. -/
structure Protocol (n : ℕ) (F : Type) [Fintype F] where
  St : Type
  M : Type
  Hd : Type
  mbits : M → ℕ
  hbits : Hd → ℕ
  init : Fin n → Bool → St
  ops : Fin n → St → List (HOp F)
  meas : Fin n → St → List ℕ
  out : Fin n → St → List (List ℕ) → List (ℕ × F) → St × List (Fin n × M) × List (Fin n × List (Hd × ℕ))
  recv : Fin n → St → List (Fin n × M) → List (Fin n × List (Hd × ℕ)) → St
  decision : St → Option Bool
  halted : St → Bool

/-- An adversary: computationally unbounded, full information.  Every choice is an arbitrary
function of the classical history.  In each adversarial micro-step it applies an instrument to
registers it may access (registers of corrupted processes, its own memory, or fresh registers it
claims), and then, seeing the outcome, may corrupt one more process.  At delivery it chooses the
classical and quantum messages sent in the name of corrupted processes (claimed sender,
recipient, content); the quantum ones must consist of registers it can access. -/
structure Adversary (n : ℕ) (F : Type) [Fintype F] [DecidableEq F] (M Hd : Type) where
  instr : History F → AdvInstr F
  corrupt : History F → Option (Fin n)
  sendC : History F → List (Fin n × Fin n × M)
  sendQ : History F → List (Fin n × Fin n × List (Hd × ℕ))

/-- Owner of a register: never allocated, the adversary's memory, or a process. -/
inductive Owner (n : ℕ) where
  | none : Owner n
  | adv : Owner n
  | proc : Fin n → Owner n
  deriving DecidableEq

/-- The classical configuration of an execution. -/
structure Cfg (n : ℕ) (F : Type) [Fintype F] (P : Protocol n F) where
  st : Fin n → P.St
  bad : Finset (Fin n)
  own : ℕ → Owner n
  next : ℕ
  stagedC : List (Fin n × Fin n × P.M)
  stagedQ : List (Fin n × Fin n × List (P.Hd × ℕ))
  /-- qubits and classical bits charged in the current round (charged at staging) -/
  roundQ : ℕ
  roundC : ℕ

section Semantics

variable {n : ℕ} {F : Type} [Fintype F] [DecidableEq F] [Zero F] {P : Protocol n F}

/-- Number of micro-steps per round: `n+1` adversarial micro-steps at the start of the round
(after the previous delivery), the honest computation step, `n+1` adversarial micro-steps
(rushing: after all honest messages of the round are staged and visible), and delivery. -/
def stepsPerRound (n : ℕ) : ℕ := 2 * n + 4

/-- Can the adversary act on register `r`? (its own, a corrupted process's, or unallocated) -/
def Cfg.accessible (c : Cfg n F P) (r : ℕ) : Prop :=
  match c.own r with
  | .none => True
  | .adv => True
  | .proc p => p ∈ c.bad

instance (c : Cfg n F P) (r : ℕ) : Decidable (c.accessible r) := by
  unfold Cfg.accessible; split <;> infer_instance

/-- Initial configuration for input vector `x`. -/
def initCfg (P : Protocol n F) (x : Fin n → Bool) : Cfg n F P where
  st := fun p => P.init p (x p)
  bad := ∅
  own := fun _ => .none
  next := 0
  stagedC := []
  stagedQ := []
  roundQ := 0
  roundC := 0

/-- Adversarial micro-step: instrument (invalid register lists are replaced by the trivial
instrument), outcome `o`, then an optional corruption of one more process, only while fewer than
`t` processes are corrupted (so at most `t` processes are ever corrupted). -/
noncomputable def advStep (A : Adversary n F P.M P.Hd) (t : ℕ) (h : History F)
    (c : Cfg n F P) (ρ : QState F) (o : Outcome F) : Cfg n F P × QState F :=
  let I0 := A.instr h
  let I := if ∀ r ∈ I0.regs, c.accessible r then I0 else AdvInstr.trivial F
  let ρ' : QState F := match o with
    | .adv i => if hi : i < I.k then applyKraus I.regs.get (I.K ⟨i, hi⟩) ρ else 0
    | _ => 0
  let own' : ℕ → Owner n := fun r => if r ∈ I.regs ∧ c.own r = .none then .adv else c.own r
  let next' := max c.next (I.regs.foldr (fun r m => max (r + 1) m) 0)
  let bad' := match A.corrupt (h ++ [o]) with
    | some p => if p ∉ c.bad ∧ c.bad.card < t then insert p c.bad else c.bad
    | none => c.bad
  ({ c with own := own', next := next', bad := bad' }, ρ')

/-- Register ids given to the slots of an honest operation when the allocation counter is `m`:
an existing register keeps its id, and the `j`-th fresh slot gets `m + j`. -/
def slotRegs {F : Type} [Fintype F] (o : HOp F) (m : ℕ) : Fin o.slots.length → ℕ :=
  fun i => match o.slots.get i with
    | some r => r
    | none => m + ((o.slots.take i.1).filter Option.isNone).length

/-- Number of fresh registers of an honest operation. -/
def HOp.fresh {F : Type} [Fintype F] (o : HOp F) : ℕ := (o.slots.filter Option.isNone).length

/-- Apply the operations of process `p` in order.  An operation whose existing slots are not all
registers owned by `p` (or which repeats a register) is skipped (its register list is reported as
empty, so the reported lists stay aligned with the operations). Returns the new state, owner map,
allocation counter and the list of resolved register lists of the applied operations. -/
noncomputable def applyOps (p : Fin n) :
    List (HOp F) → QState F → (ℕ → Owner n) → ℕ → QState F × (ℕ → Owner n) × ℕ × List (List ℕ)
  | [], ρ, own, m => (ρ, own, m, [])
  | o :: os, ρ, own, m =>
    let reg := slotRegs o m
    let ok : Prop := (∀ i, ∀ r, o.slots.get i = some r → own r = .proc p) ∧ Function.Injective reg
    by classical exact
      if ok then
        let own' : ℕ → Owner n := fun r => if m ≤ r ∧ r < m + o.fresh then .proc p else own r
        let rest := applyOps p os (applyKraus reg o.op ρ) own' (m + o.fresh)
        (rest.1, rest.2.1, rest.2.2.1, (List.ofFn reg) :: rest.2.2.2)
      else
        let rest := applyOps p os ρ own m
        (rest.1, rest.2.1, rest.2.2.1, [] :: rest.2.2.2)

/-- Classical bits charged for staged messages (at least one per channel use). -/
def chargeC (P : Protocol n F) (cs : List (Fin n × P.M)) (qs : List (Fin n × List (P.Hd × ℕ))) : ℕ :=
  (cs.map (fun m => max 1 (P.mbits m.2))).sum + (qs.map (fun m => (m.2.map (fun e => P.hbits e.1)).sum)).sum

/-- Qubits charged for staged quantum messages: `d = log₂ q` qubits per register, at least one
per channel use. -/
def chargeQ (P : Protocol n F) (qs : List (Fin n × List (P.Hd × ℕ))) : ℕ :=
  (qs.map (fun m => max 1 (Nat.log 2 (Fintype.card F) * m.2.length))).sum

/-- Is process `p` active (honest and not halted) in configuration `c`? -/
def Cfg.active (c : Cfg n F P) (p : Fin n) : Prop := p ∉ c.bad ∧ P.halted (c.st p) = false

/-- The honest computation micro-step of a round.  Every active process applies its operations
(in process order), then all active processes measure their requested registers (only registers
they own) in the computational basis; the outcome `meas v` lists all outcomes in process order.
Each active process then updates its state and stages its messages; staged transmissions are
charged now (even if the sender is corrupted later in the round). -/
noncomputable def honestStep (P : Protocol n F) (c : Cfg n F P) (ρ : QState F) (o : Outcome F) :
    Cfg n F P × QState F := by
  classical
  let procs := List.finRange n
  -- quantum operations, process by process
  let step1 : (QState F × (ℕ → Owner n) × ℕ × (Fin n → List (List ℕ))) → Fin n →
      (QState F × (ℕ → Owner n) × ℕ × (Fin n → List (List ℕ))) := fun acc p =>
    if c.active p then
      let r := applyOps p (P.ops p (c.st p)) acc.1 acc.2.1 acc.2.2.1
      (r.1, r.2.1, r.2.2.1, Function.update acc.2.2.2 p r.2.2.2)
    else acc
  let s1 := procs.foldl step1 (ρ, c.own, c.next, fun _ => [])
  let own1 := s1.2.1
  -- measurements
  let mlist : Fin n → List ℕ := fun p =>
    if c.active p then (P.meas p (c.st p)).filter (fun r => own1 r = .proc p) |>.dedup else []
  let allM := (procs.map mlist).flatten
  let offs : Fin n → ℕ := fun p => ((procs.filter (fun q => q < p)).map (fun q => (mlist q).length)).sum
  let vals : List F := match o with
    | .meas v => v
    | _ => []
  let ρ2 : QState F := match o with
    | .meas v => if allM.Nodup then applyKraus allM.get (measProj allM v) s1.1 else 0
    | _ => 0
  -- local updates and staging
  let res : Fin n → P.St × List (Fin n × P.M) × List (Fin n × List (P.Hd × ℕ)) := fun p =>
    P.out p (c.st p) (s1.2.2.2 p) (List.zip (mlist p) ((vals.drop (offs p)).take (mlist p).length))
  let st' : Fin n → P.St := fun p => if c.active p then (res p).1 else c.st p
  let sc : List (Fin n × Fin n × P.M) :=
    (procs.filter (fun p => c.active p)).flatMap (fun p => (res p).2.1.map (fun m => (p, m.1, m.2)))
  let sq : List (Fin n × Fin n × List (P.Hd × ℕ)) :=
    (procs.filter (fun p => c.active p)).flatMap (fun p =>
      (res p).2.2.map (fun m => (p, m.1, m.2.filter (fun e => own1 e.2 = .proc p))))
  let qc := ((procs.filter (fun p => c.active p)).map (fun p => chargeQ P (res p).2.2)).sum
  let cc := ((procs.filter (fun p => c.active p)).map (fun p => chargeC P (res p).2.1 (res p).2.2)).sum
  exact (Cfg.mk st' c.bad own1 s1.2.2.1 sc sq qc cc, ρ2)

/-- Delivery at the end of a round.  Staged messages of senders still honest are delivered
unchanged (their registers move to the recipient); messages of senders corrupted during the round
are not (the adversary holds their staged registers); in addition the adversary delivers messages
in the name of corrupted processes, quantum ones built from registers it can access.  Every
honest, non-halted process then receives its messages. -/
noncomputable def deliverStep (P : Protocol n F) (A : Adversary n F P.M P.Hd) (h : History F)
    (c : Cfg n F P) (ρ : QState F) (o : Outcome F) : Cfg n F P × QState F := by
  classical
  let hc := c.stagedC.filter (fun m => m.1 ∉ c.bad)
  let hq := c.stagedQ.filter (fun m => m.1 ∉ c.bad)
  let ac := (A.sendC h).filter (fun m => m.1 ∈ c.bad)
  let aq0 := (A.sendQ h).filter (fun m => m.1 ∈ c.bad)
  -- honest quantum deliveries
  let own1 : ℕ → Owner n := fun r =>
    match hq.find? (fun m => m.2.2.any (fun e => e.2 = r)) with
    | some m => .proc m.2.1
    | none => c.own r
  -- adversarial quantum deliveries, processed in order; a register is used only if accessible
  let stepQ : ((ℕ → Owner n) × List (Fin n × Fin n × List (P.Hd × ℕ))) → (Fin n × Fin n × List (P.Hd × ℕ)) →
      ((ℕ → Owner n) × List (Fin n × Fin n × List (P.Hd × ℕ))) := fun acc m =>
    let ok : ℕ → Prop := fun r => match acc.1 r with
      | .none => False
      | .adv => True
      | .proc p => p ∈ c.bad
    let es := (m.2.2.filter (fun e => ok e.2)).foldl
      (fun l e => if l.any (fun e' => e'.2 = e.2) then l else l ++ [e]) []
    (fun r => if es.any (fun e => e.2 = r) then .proc m.2.1 else acc.1 r, acc.2 ++ [(m.1, m.2.1, es)])
  let s2 := aq0.foldl stepQ (own1, [])
  let allC := hc ++ ac
  let allQ := hq ++ s2.2
  let inC : Fin n → List (Fin n × P.M) := fun p => (allC.filter (fun m => m.2.1 = p)).map (fun m => (m.1, m.2.2))
  let inQ : Fin n → List (Fin n × List (P.Hd × ℕ)) := fun p => (allQ.filter (fun m => m.2.1 = p)).map (fun m => (m.1, m.2.2))
  let st' : Fin n → P.St := fun p => if c.active p then P.recv p (c.st p) (inC p) (inQ p) else c.st p
  let ρ' : QState F := match o with
    | .tick => ρ
    | _ => 0
  exact (Cfg.mk st' c.bad s2.1 c.next [] [] c.roundQ c.roundC, ρ')

/-- The micro-step with global index `k`, given the history `h` of the previous outcomes. -/
noncomputable def stepAt (P : Protocol n F) (A : Adversary n F P.M P.Hd) (t : ℕ) (k : ℕ)
    (h : History F) (s : Cfg n F P × QState F) (o : Outcome F) : Cfg n F P × QState F :=
  let i := k % stepsPerRound n
  if i < n + 1 then advStep A t h s.1 s.2 o
  else if i = n + 1 then honestStep P s.1 s.2 o
  else if i < 2 * n + 3 then advStep A t h s.1 s.2 o
  else deliverStep P A h s.1 s.2 o

/-- Run the remaining outcomes `os` after the already processed history `h`. -/
noncomputable def runFrom (P : Protocol n F) (A : Adversary n F P.M P.Hd) (t : ℕ) :
    History F → List (Outcome F) → Cfg n F P × QState F → Cfg n F P × QState F
  | _, [], s => s
  | h, o :: os, s => runFrom P A t (h ++ [o]) os (stepAt P A t h.length h s o)

/-- Classical configuration and unnormalized quantum branch state after the history `h`, for
input vector `x`, adversary `A` and corruption bound `t`. -/
noncomputable def run (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (h : History F) : Cfg n F P × QState F :=
  runFrom P A t [] h (initCfg P x, initState)

/-- Probability weight of a history: the trace of its unnormalized branch state. -/
noncomputable def weight (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (h : History F) : ℝ :=
  (traceN (run P x A t h).1.next (run P x A t h).2).re

/-- Conditional law of the next outcome after history `h` (Born rule): the weights of the
one-step extensions, normalized (normalization is the identity whenever `weight h > 0`, because
all operations are trace preserving on the reachable states). -/
noncomputable def stepPMF (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (h : History F) : PMF (Outcome F) :=
  let w : Outcome F → ℝ≥0∞ := fun o => ENNReal.ofReal (weight P x A t (h ++ [o]))
  by classical exact
    if hs : (∑' o, w o) ≠ 0 ∧ (∑' o, w o) ≠ ⊤ then PMF.normalize w hs.1 hs.2 else PMF.pure .tick

/-- The history encoded by the coordinates `1, …, k` of a trajectory prefix. -/
def histOfPi {F : Type} (k : ℕ) (f : Π _i : Finset.Iic k, Outcome F) : History F :=
  (List.range k).map (fun i => if hi : i + 1 ≤ k then f ⟨i + 1, Finset.mem_Iic.mpr hi⟩ else .tick)

/-- The transition kernels of the execution. -/
noncomputable def stepKernel [Countable F] (P : Protocol n F) (x : Fin n → Bool)
    (A : Adversary n F P.M P.Hd) (t : ℕ) (k : ℕ) :
    ProbabilityTheory.Kernel (Π _i : Finset.Iic k, Outcome F) (Outcome F) :=
  ProbabilityTheory.Kernel.ofFunOfCountable (fun f => (stepPMF P x A t (histOfPi k f)).toMeasure)

instance [Countable F] (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (k : ℕ) : ProbabilityTheory.IsMarkovKernel (stepKernel P x A t k) :=
  ⟨fun f => PMF.toMeasure.isProbabilityMeasure (stepPMF P x A t (histOfPi k f))⟩

/-- The law of the infinite execution (Ionescu-Tulcea): a probability measure on infinite outcome
sequences; coordinate `0` is a dummy `tick`, coordinate `k+1` is the outcome of micro-step `k`. -/
noncomputable def execMeasure [Countable F] (P : Protocol n F) (x : Fin n → Bool)
    (A : Adversary n F P.M P.Hd) (t : ℕ) : MeasureTheory.Measure (ℕ → Outcome F) :=
  ProbabilityTheory.Kernel.trajMeasure (MeasureTheory.Measure.dirac Outcome.tick) (stepKernel P x A t)

/-- The history formed by the first `k` micro-step outcomes of an infinite execution. -/
def prefixH {F : Type} (ω : ℕ → Outcome F) (k : ℕ) : History F := (List.range k).map (fun i => ω (i + 1))

/-! ## Executions, correctness, decisions, costs -/

/-- An execution: an infinite outcome sequence every finite prefix of which has positive
probability. -/
def IsExecution (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) : Prop :=
  ∀ k, 0 < weight P x A t (prefixH ω k)

/-- Configuration after the first `k` micro-steps of `ω`. -/
noncomputable def cfgAt (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) (k : ℕ) : Cfg n F P :=
  (run P x A t (prefixH ω k)).1

/-- `p` is correct on `ω`: never corrupted. -/
def IsCorrect (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) (p : Fin n) : Prop :=
  ∀ k, p ∉ (cfgAt P x A t ω k).bad

/-- Agreement: on every execution, all correct processes that decide decide the same bit. -/
def Agreement (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ) : Prop :=
  ∀ ω, IsExecution P x A t ω → ∀ p q, IsCorrect P x A t ω p → IsCorrect P x A t ω q →
    ∀ k k' v v', P.decision ((cfgAt P x A t ω k).st p) = some v →
      P.decision ((cfgAt P x A t ω k').st q) = some v' → v = v'

/-- Validity: on every execution, if all correct processes have input `v`, every decision of a
correct process is `v`. -/
def Validity (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ) : Prop :=
  ∀ ω, IsExecution P x A t ω → ∀ v : Bool, (∀ p, IsCorrect P x A t ω p → x p = v) →
    ∀ p, IsCorrect P x A t ω p → ∀ k v', P.decision ((cfgAt P x A t ω k).st p) = some v' → v' = v

/-- `p` has decided and halted after the first `k` micro-steps. -/
def DecidedHalted (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) (p : Fin n) (k : ℕ) : Prop :=
  P.halted ((cfgAt P x A t ω k).st p) = true ∧ (P.decision ((cfgAt P x A t ω k).st p)).isSome

/-- Termination: with probability 1, every correct process decides and halts. -/
def Termination [Countable F] (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd)
    (t : ℕ) : Prop :=
  execMeasure P x A t {ω | ∃ p, IsCorrect P x A t ω p ∧ ¬ ∃ k, DecidedHalted P x A t ω p k} = 0

/-- Index of the boundary at the end of round `r` (rounds are numbered from `0`). -/
def endOfRound (n r : ℕ) : ℕ := (r + 1) * stepsPerRound n

/-- The round in which `p` halts (`⊤` if it never halts). -/
noncomputable def haltRound (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) (p : Fin n) : ℕ∞ :=
  ⨅ (r : ℕ) (_ : P.halted ((cfgAt P x A t ω (endOfRound n r)).st p) = true), (r : ℕ∞)

/-- `R`: the number of rounds through the last halt of a correct process. -/
noncomputable def roundsR (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) : ℕ∞ :=
  ⨆ (p : Fin n) (_ : IsCorrect P x A t ω p), (haltRound P x A t ω p + 1)

/-- `Q`: qubits sent by honest processes in the rounds through the last correct halt. -/
noncomputable def costQ (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) : ℝ≥0∞ :=
  ∑' r : ℕ, if (r : ℕ∞) < roundsR P x A t ω then ((cfgAt P x A t ω (endOfRound n r)).roundQ : ℝ≥0∞) else 0

/-- `C`: classical bits sent by honest processes in the rounds through the last correct halt. -/
noncomputable def costC (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd) (t : ℕ)
    (ω : ℕ → Outcome F) : ℝ≥0∞ :=
  ∑' r : ℕ, if (r : ℕ∞) < roundsR P x A t ω then ((cfgAt P x A t ω (endOfRound n r)).roundC : ℝ≥0∞) else 0

/-- Expected value of an `ℝ≥0∞`-valued function of the execution. -/
noncomputable def expect [Countable F] (P : Protocol n F) (x : Fin n → Bool) (A : Adversary n F P.M P.Hd)
    (t : ℕ) (X : (ℕ → Outcome F) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, X ω ∂(execMeasure P x A t)

end Semantics

end QuantumBA.PackedShares


