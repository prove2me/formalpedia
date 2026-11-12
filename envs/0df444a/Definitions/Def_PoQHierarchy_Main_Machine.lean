-- Prove2me | Definitions.Def_PoQHierarchy_Main_Machine
-- name    : PoQHierarchy_Main_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:47.850199+00:00
-- url     : https://prove2.me/theorems/893da9fb-f761-41e1-a68c-42abe7a8af44
-- title:
--   $\mathsf{PPT}^{k\text{-intQPT}}$: uniform classical machines with at most $k$ invocations of a persistent quantum device
-- statement:
--   This file defines the computational model of Definition 4.1 for every $k\in\mathbb N_0\cup\{\infty\}$.
--
--   A **machine** consists of polynomially bounded functions giving, in terms of the input length $|x|$, its number of random coins, the size of its device workspace, its maximal number of actions and the maximal length of an action string, together with one **next-action function** $\delta:\{0,1\}^*\to\{0,1\}^*$. On input $x$ and coins $r$, after a history $h$ of the interaction, the machine takes the action $\delta(\langle x,r,h\rangle)$, which is one of
--
--   1. $\mathsf{query}(c)$: invoke the device with circuit description $c$;
--   2. $\mathsf{send}(a)$: send the message $a$ to its environment (a verifier or an oracle), which replies or closes the interaction;
--   3. $\mathsf{halt}(o)$: stop with output $o$.
--
--   The history records every received message, every sent message and every invocation with its reply. A run that exceeds its action budget, or produces an action string longer than its bound, is aborted. The **execution** of a machine is the resulting distribution over (ending, messages sent, final device state), over its coins, the environment's randomness and the Born rule.
--
--   The machine is **efficient** if the four bounds are polynomial and $\delta$ is computed by a polynomial-time Turing machine (the published `PolyTimeComputable`; uniformity, p.23). Then the whole run takes polynomial time. It satisfies the **invocation limit $k$** if, on every input and coins, after every history consistent with its own actions, it issues an invocation only while fewer than $k$ invocations have been made. Then
--   $$\mathsf{PPT}^{k\text{-intQPT}}=\{M : M\text{ efficient and with invocation limit }k\},\qquad \mathsf{PPT}=\mathsf{PPT}^{0\text{-intQPT}},\qquad \mathsf{QPT}=\mathsf{PPT}^{\infty\text{-intQPT}}.$$
--
--   This model is the one used for provers, for the algorithms of a QFHE scheme and for its adversaries, so that a prover is itself a legitimate adversary.
--
--   **Formalization Note** The paper's alternative reading (p.25: queries after the $k$-th return $\perp$) is equivalent: a machine can count its own queries. Histories are quantified over all received messages and device replies, so the limit holds in every execution and every environment.
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), Definition 4.1 (pp.24–25), p.23 (uniform models), p.25 (PPT^{0-intQPT} = PPT, PPT^{∞-intQPT} = QPT); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Device

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, Definition 4.1 (pp.24–25):
probabilistic-`k`-interactive-quantum polynomial-time algorithms `PPT^{k-intQPT}`.

An algorithm is a uniform classical machine, given by one polynomial-time next-action function
`next : {0,1}* → {0,1}*` (the published `QAlgorithms.Complexity.PolyTimeComputable`, Mathlib's
`Turing.TM2ComputableInPolyTime`). Its configuration is the string coding its input, its random
coins and the whole history of the interaction so far. Each action is

* `query c`: send the classical description `c` of a circuit to the device, which runs it on its
  persistent workspace (initialised to `|0…0⟩` once, never reset) and returns the classical outcome;
* `send a`: send the message `a` to the environment (a verifier, or an oracle), which replies;
* `halt o`: stop with output `o`.

Polynomial bounds on the number of coins, the number of qubits, the number of actions and the length
of each action string make the total running time polynomial. An algorithm is in `PPT^{k-intQPT}` if
it makes at most `k` device invocations (`k : ℕ∞`), whatever it has observed so far.
-/

/-- One entry of the history of an interaction. -/
inductive Event
  /-- a message received from the environment -/
  | recv (q : Str)
  /-- a message sent to the environment -/
  | sent (a : Str)
  /-- a device invocation with description `c` and reply `r` (`none` is the error symbol `⊥`) -/
  | query (c : Str) (r : Option Str)

/-- The code of a history entry. -/
def Event.code : Event → Str
  | .recv q => pack [[false, false], q]
  | .sent a => pack [[false, true], a]
  | .query c none => pack [[true, false], c]
  | .query c (some m) => pack [[true, true], c, m]

/-- Whether a history entry is a device invocation. -/
def Event.isQuery : Event → Bool
  | .query _ _ => true
  | _ => false

/-- Whether a history entry is a sent message. -/
def Event.isSent : Event → Bool
  | .sent _ => true
  | _ => false

/-- Whether a history entry is a received message. -/
def Event.isRecv : Event → Bool
  | .recv _ => true
  | _ => false

/-- The actions of the classical machine. -/
inductive Action
  | query (c : Str)
  | send (a : Str)
  | halt (o : Str)

/-- Reading an action off the output of the next-action function: `00c` is `query c`, `01a` is
`send a`, `1o` is `halt o`; anything else halts with the empty output. -/
def decodeAction : Str → Action
  | false :: false :: c => .query c
  | false :: true :: a => .send a
  | true :: o => .halt o
  | _ => .halt []

/-- A classical machine with classical access to a quantum device (Definition 4.1). All bounds are
functions of the input length. -/
structure IntMachine where
  /-- number of uniformly random coins -/
  coins : ℕ → ℕ
  /-- number of qubits of the device workspace -/
  qubits : ℕ → ℕ
  /-- maximal number of actions -/
  steps : ℕ → ℕ
  /-- maximal length of an action string -/
  width : ℕ → ℕ
  /-- the next-action function on configurations -/
  next : Str → Str

/-- The configuration: input, coins and history. -/
def config (x r : Str) (hist : List Event) : Str := pack [x, r, pack (hist.map Event.code)]

/-- The action the machine takes on input `x`, coins `r` and history `hist`. -/
def IntMachine.action (M : IntMachine) (x r : Str) (hist : List Event) : Action :=
  decodeAction (M.next (config x r hist))

/-- How a run ends. -/
inductive Ending
  /-- the machine halted with an output -/
  | halted (o : Str)
  /-- the environment closed the interaction after the machine's last message -/
  | finished
  /-- the machine exceeded its action budget or the length bound of an action -/
  | aborted
  deriving DecidableEq

/-- An environment: given the list of messages the machine has sent so far, the distribution of its
reply (`none` closes the interaction). Its value on `[]` is the environment's opening message. -/
abbrev Env := List Str → WList (Option Str)

/-- The empty environment: no opening message, and every message closes the interaction. -/
def noEnv : Env := fun _ => WList.pure none

/-- The run of `M` from a history, with `fuel` actions left, on a device of `W` qubits of which the
first `addr` are addressable. Each branch carries the classical weight (from the environment's
randomness), how the run ended, the messages sent, and the unnormalized device state; the
probability of the branch is the weight times the squared norm of the state. -/
noncomputable def IntMachine.runCore (M : IntMachine) (x r : Str) (env : Env) (addr W : ℕ) :
    ℕ → List Event → List Str → QVec W → WList (Ending × List Str × QVec W)
  | 0, _, sent, ψ => WList.pure (.aborted, sent, ψ)
  | fuel + 1, hist, sent, ψ =>
    let s := M.next (config x r hist)
    if M.width x.length < s.length then WList.pure (.aborted, sent, ψ) else
    match decodeAction s with
    | .query c =>
      (deviceStep addr W c ψ).flatMap fun p =>
        M.runCore x r env addr W fuel (hist ++ [.query c p.1]) sent p.2
    | .send a =>
      (env (sent ++ [a])).bind fun rep =>
        match rep with
        | none => WList.pure (.finished, sent ++ [a], ψ)
        | some q => M.runCore x r env addr W fuel (hist ++ [.sent a, .recv q]) (sent ++ [a]) ψ
    | .halt o => WList.pure (.halted o, sent, ψ)

/-- The execution of `M` on input `x` in environment `env`, with the device holding `ψ0` on `W`
qubits of which the first `addr` are addressable: uniform coins, the environment's opening message,
then at most `M.steps |x|` actions. -/
noncomputable def IntMachine.exec (M : IntMachine) (x : Str) (env : Env) (addr W : ℕ)
    (ψ0 : QVec W) : WList (Ending × List Str × QVec W) :=
  (coinDist (M.coins x.length)).bind fun r =>
    (env []).bind fun first =>
      M.runCore x r env addr W (M.steps x.length)
        (match first with
          | none => []
          | some q => [.recv q]) [] ψ0

/-- The distribution of (ending, messages sent) when `M` runs on a fresh device of
`M.qubits |x|` qubits in `|0…0⟩`; Born weights included. -/
noncomputable def IntMachine.outcomes (M : IntMachine) (x : Str) (env : Env) :
    WList (Ending × List Str) :=
  (M.exec x env (M.qubits x.length) (M.qubits x.length) (zeroVec _)).map
    fun p => (p.1 * normSq p.2.2.2, (p.2.1, p.2.2.1))

/-- The output distribution of `M` on input `x` (no environment): `some o` if it halts with
output `o`, `none` otherwise. -/
noncomputable def IntMachine.outDist (M : IntMachine) (x : Str) : WList (Option Str) :=
  (M.outcomes x noEnv).map fun p =>
    (p.1, match p.2.1 with
      | .halted o => some o
      | _ => none)

/-- Efficiency: polynomially many coins, qubits and actions, actions of polynomial length, and a
polynomial-time next-action function (uniformity, p.23). -/
def IntMachine.Efficient (M : IntMachine) : Prop :=
  PolyBounded M.coins ∧ PolyBounded M.qubits ∧ PolyBounded M.steps ∧ PolyBounded M.width ∧
    PolyTimeComputable M.next

/-- A history is consistent with `M` (on input `x` and coins `r`): every query and every sent
message in it is the action `M` takes on the history before it. Received messages and device
replies are arbitrary. -/
def IntMachine.Consistent (M : IntMachine) (x r : Str) (hist : List Event) : Prop :=
  ∀ (j : ℕ) (h : j < hist.length),
    match hist[j] with
    | .query c _ => M.action x r (hist.take j) = .query c
    | .sent a => M.action x r (hist.take j) = .send a
    | .recv _ => True

/-- *Invocation Limit* (Definition 4.1): on every input and all coins, after any history consistent
with its own actions (whatever messages and device outputs it received), the machine issues an
invocation only while fewer than `k` invocations have been made. Hence every run makes at most `k`
invocations. -/
def IntMachine.QueryBounded (M : IntMachine) (k : ℕ∞) : Prop :=
  ∀ (x r : Str) (hist : List Event) (c : Str), M.Consistent x r hist →
    M.action x r hist = .query c → (((hist.filter Event.isQuery).length : ℕ) : ℕ∞) < k

/-- **`PPT^{k-intQPT}`** (Definition 4.1), for `k ∈ ℕ ∪ {∞}`. -/
def PPTk (k : ℕ∞) : Set IntMachine := {M | M.Efficient ∧ M.QueryBounded k}

/-- `PPT = PPT^{0-intQPT}` (p.25). -/
def PPT : Set IntMachine := PPTk 0

/-- `QPT = PPT^{∞-intQPT}` (p.25). -/
def QPT : Set IntMachine := PPTk ⊤

end PoQHierarchy.Main


