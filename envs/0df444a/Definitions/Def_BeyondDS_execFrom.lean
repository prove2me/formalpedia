-- Prove2me | Definitions.Def_BeyondDS_execFrom
-- name    : BeyondDS_execFrom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:55.900216+00:00
-- url     : https://prove2.me/theorems/3924b3da-6eb6-4239-92f7-a4f470d7c5fe
-- title:
--   The synchronous network model with adaptive corruptions and a late common election
-- statement:
--   This is the probabilistic execution of a protocol $\Pi$ with scheme $\Sigma$, parameters $P$, sender input $x$, election law $E$ and adversary $A$.
--
--   1. **Activation.** An activated honest player runs its transition through internal operations (sign, verify, sample, decide) up to and including its next send, yield or halt; with no operation left in its round budget it has yielded. A fresh random destination and the send that uses it therefore cannot be separated by the adversary, while two sends can: "Fresh random destinations are sampled privately immediately before their transmissions … This does not assume an atomic multicast or an atomic sequence of random transmissions."
--   2. **Moves.** At each move the adversary sees its pending observations and decides. Corruptions are permanent, reveal state and key, and a move that would exceed the budget $t$ is ignored for its corruptions; a move with a new corruption hands control straight back. Injected messages go only through corrupted identities ("channels identify their immediate sender"). Otherwise the named player acts if it can, else the least player that can; when nobody can, the round ends. So the adversary can interrupt a sender between sends and cannot stall an honest player.
--   3. **Delivery boundary.** Every message committed in the round reaches its recipient if the recipient is uncorrupted; it cannot be removed. Then, if the public schedule says so, a fresh election output drawn from $E$ (given the transcript) is revealed to all active players and to the adversary.
--   4. **Execution.** Rounds run up to the public round cap, followed by one local computation in which players may decide but not send (the public final deadline). The whole execution starts with honest key generation and nobody corrupted.
--
--   The ideal election draws an independent uniform identity, whatever the transcript; an election law is at statistical distance at most $\zeta$ from uniform when $E(h)(U)\le |U|/n+\zeta$ for every transcript $h$ and set $U$.
--
--   **Formalization Note** The election is revealed at the boundary, after every send of that round, so it is "late": the adversary cannot obtain it earlier, even from corrupted states. Started from a configuration in the support of a prefix, `execFrom` is the conditional law of the continuation, since a configuration holds all history.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §4.1, pp.11–12 (PDF pp.12–13); §4.3, p.13 (PDF p.14); §5.1, p.14 (PDF p.15); §7.1, pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_BeyondDS_Config

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

variable {n : ℕ} {Msg St σ : Type}

namespace Config

/-- Add an observation for the adversary, and log it. -/
def push (c : Config n Msg St σ) (o : Obs n Msg St) : Config n Msg St σ :=
  { c with obs := c.obs ++ [o], log := c.log ++ [Event.obs o] }

/-- Replace the pending answer of `i`. -/
def setResp (c : Config n Msg St σ) (i : Fin n) (r : Resp Msg) : Config n Msg St σ :=
  { c with resp := Function.update c.resp i r }

/-- Log the signatures of a batch and answer it. -/
def afterSign (c : Config n Msg St σ) (i : Fin n) (ms ss : List Str) : Config n Msg St σ :=
  { c with
    signLog := c.signLog ++ ms.map fun m => (i, m)
    log := c.log ++ ms.map fun m => Event.signed i m
    resp := Function.update c.resp i (Resp.signatures ss) }

/-- Whether a signature of identity `j` on `m` verifies. -/
def checks (c : Config n Msg St σ) (S : Sig) (j : ℕ) (m s : Str) : Bool :=
  if h : j < n then S.accepts (c.pk ⟨j, h⟩) m s else false

/-- The forgeries in a batch of verifications: a signature that verifies, attributed to an identity
that is currently uncorrupted, on a message that identity has not yet signed (§4.2, p.12). -/
def forgeries (c : Config n Msg St σ) (S : Sig) (i : Fin n) (qs : List (ℕ × Str × Str)) :
    List (Event n Msg St) :=
  (List.finRange n).flatMap fun j =>
    (qs.filter fun q =>
      q.1 = j.val ∧ c.checks S q.1 q.2.1 q.2.2 = true ∧ j ∉ c.corrupted ∧
        (j, q.2.1) ∉ c.signLog).map fun q => Event.forgery i j q.2.1

/-- Answer a batch of verifications, logging its forgeries. -/
def afterVerify (c : Config n Msg St σ) (S : Sig) (i : Fin n) (qs : List (ℕ × Str × Str)) :
    Config n Msg St σ :=
  { c with
    log := c.log ++ c.forgeries S i qs
    resp := Function.update c.resp i
      (Resp.verdicts (qs.map fun q => c.checks S q.1 q.2.1 q.2.2)) }

/-- A committed transmission: visible to the adversary, and in the recipient's inbox, irrevocably. -/
def afterSend (c : Config n Msg St σ) (i : Fin n) (j : ℕ) (m : Msg) : Config n Msg St σ :=
  let c := c.setResp i Resp.done
  if h : j < n then
    ({ c with
      inbox := Function.update c.inbox ⟨j, h⟩ (c.inbox ⟨j, h⟩ ++ [(i.val, m)]) }).push
        (Obs.sent i ⟨j, h⟩ m)
  else c

/-- Record the first decision. -/
def afterDecide (c : Config n Msg St σ) (i : Fin n) (b : Bool) : Config n Msg St σ :=
  { c with
    decision := Function.update c.decision i ((c.decision i).orElse fun _ => some b)
    resp := Function.update c.resp i Resp.done }

end Config

/-- A fresh private value uniform on `{0, …, N}`. -/
noncomputable def sampleLaw (N : ℕ) : PMF ℕ :=
  (PMF.uniformOfFintype (Fin (N + 1))).map Fin.val

/-- One activation of the honest player `i` with `f` operations left: run `next` through internal
operations up to and including the next `send`, `yield` or `halt` (§4.1, p.12: "Fresh random
destinations are sampled privately immediately before their transmissions"). A `sample` and the `send`
after it therefore cannot be separated by the adversary, while two sends can. If `final`, this is the
local computation after the last boundary and transmissions are dropped. With no operation left, the
player has yielded. -/
noncomputable def runOps (S : Sig) (next : St → Resp Msg → Op Msg × St) (final : Bool) (i : Fin n) :
    ℕ → Config n Msg St σ → PMF (Config n Msg St σ)
  | 0, c =>
    PMF.pure { c with yielded := Function.update c.yielded i true, budget := Function.update c.budget i 0 }
  | f + 1, c =>
    match next (c.st i) (c.resp i) with
    | (op, s) =>
      let c := { c with st := Function.update c.st i s }
      match op with
      | Op.signAll ms =>
        (S.signBatch (c.sk i) ms).bind fun ss => runOps S next final i f (c.afterSign i ms ss)
      | Op.verifyAll qs => runOps S next final i f (c.afterVerify S i qs)
      | Op.sample N =>
        (sampleLaw N).bind fun k => runOps S next final i f (c.setResp i (Resp.sampled k))
      | Op.send j m =>
        if final then runOps S next final i f (c.setResp i Resp.done)
        else PMF.pure { c.afterSend i j m with budget := Function.update c.budget i f }
      | Op.yield =>
        PMF.pure { c with
          yielded := Function.update c.yielded i true
          budget := Function.update c.budget i f }
      | Op.decide b => runOps S next final i f (c.afterDecide i b)
      | Op.halt =>
        PMF.pure { c with
          active := Function.update c.active i false
          yielded := Function.update c.yielded i true
          budget := Function.update c.budget i f }

namespace Config

/-- Activate `i`, and log its state at the end of the activation. -/
noncomputable def activate (c : Config n Msg St σ) (S : Sig) (next : St → Resp Msg → Op Msg × St)
    (final : Bool) (i : Fin n) (f : ℕ) : PMF (Config n Msg St σ) :=
  (runOps S next final i f c).map fun c' => { c' with log := c'.log ++ [Event.state i (c'.st i)] }

/-- `i` can still act in this round. -/
def runnable (c : Config n Msg St σ) (i : Fin n) : Bool :=
  decide (i ∉ c.corrupted) && c.active i && !c.yielded i

/-- Apply corruptions: permanent, each revealing state and key; a move exceeding the budget `t` is
ignored for its corruptions (§4.1, p.11). -/
def corruptAll (c : Config n Msg St σ) (t : ℕ) (C : Finset (Fin n)) : Config n Msg St σ :=
  if (c.corrupted ∪ C).card ≤ t then
    ((List.finRange n).filter fun i => i ∈ C ∧ i ∉ c.corrupted).foldl
      (fun c i =>
        ({ c with
          corrupted := insert i c.corrupted
          corruptAt := Function.update c.corruptAt i (some c.round) }).push
          (Obs.revealed i (c.st i) (c.resp i) (c.sk i)))
      c
  else c

/-- Messages of the adversary, only through corrupted identities ("channels identify their immediate
sender", p.14). -/
def injectAll (c : Config n Msg St σ) (ms : List (Fin n × Fin n × Msg)) : Config n Msg St σ :=
  ms.foldl
    (fun c m =>
      if m.1 ∈ c.corrupted then
        { c with
          inbox := Function.update c.inbox m.2.1 (c.inbox m.2.1 ++ [(m.1.val, m.2.2)])
          log := c.log ++ [Event.injected m.1 m.2.1 m.2.2] }
      else c)
    c

end Config

/-- One move: the adversary sees its pending observations and decides. A move with a new corruption
hands control straight back, so the adversary can read the revealed state before acting again.
Otherwise the player it names is activated if it can act, else the least player that can; if nobody can,
the round ends (`true`). So the adversary can interrupt a sender between sends, and it cannot stall an
honest player. -/
noncomputable def move (S : Sig) (next : St → Resp Msg → Op Msg × St) (t : ℕ)
    (step : σ → List (Obs n Msg St) → PMF (σ × Decision n Msg)) (c : Config n Msg St σ) :
    PMF (Config n Msg St σ × Bool) :=
  (step c.adv c.obs).bind fun ad =>
    let c₀ : Config n Msg St σ := { c with adv := ad.1, obs := [] }
    let c₁ := c₀.corruptAll t ad.2.corrupt
    let c₂ := c₁.injectAll ad.2.inject
    if c₁.corrupted ≠ c₀.corrupted then PMF.pure (c₂, false)
    else
      let chosen : Option (Fin n) :=
        match ad.2.next with
        | some i => if c₂.runnable i then some i else (List.finRange n).find? c₂.runnable
        | none => (List.finRange n).find? c₂.runnable
      match chosen with
      | some i => (c₂.activate S next false i (c₂.budget i)).map fun c' => (c', false)
      | none => PMF.pure (c₂, true)

/-- The moves of one round. The fuel `n · opCap + n + t + 1` is never exhausted: each activation uses an
operation or is a forced yield, there are at most `t` corruption moves, and one move ends the round. -/
noncomputable def moves (S : Sig) (next : St → Resp Msg → Op Msg × St) (t : ℕ)
    (step : σ → List (Obs n Msg St) → PMF (σ × Decision n Msg)) :
    ℕ → Config n Msg St σ → PMF (Config n Msg St σ)
  | 0, c => PMF.pure c
  | f + 1, c =>
    (move S next t step c).bind fun cb =>
      if cb.2 then PMF.pure cb.1 else moves S next t step f cb.1

/-- The delivery boundary (§7.1, p.22): every message sent in the round reaches its recipient if the
recipient is uncorrupted; then the election, if public schedule says so, is revealed to all active
players and to the adversary; then the round counter moves. -/
noncomputable def boundary (elect : Bool) (E : List (Event n Msg St) → PMF (Fin n))
    (c : Config n Msg St σ) : PMF (Config n Msg St σ) :=
  (if elect then (E c.log).map some else PMF.pure none).bind fun L =>
    let c₁ := match L with
      | some l => c.push (Obs.elected c.round l)
      | none => c
    let c₂ := c₁.push (Obs.boundary c.round)
    PMF.pure { c₂ with
      resp := fun i =>
        if i ∉ c.corrupted ∧ c.active i = true then
          Resp.boundary (c.inbox i) (L.map Fin.val)
        else c.resp i
      inbox := fun _ => []
      round := c.round + 1
      doneAt := c.doneAt.orElse fun _ =>
        if ∀ i, i ∉ c.corrupted → c.active i = false then some (c.round + 1) else none }

/-- One round: every player's operation budget is reset, the moves run, and then the boundary. -/
noncomputable def oneRound (Pi : Protocol Msg St) (S : Sig) (P : Params)
    (E : List (Event P.n Msg St) → PMF (Fin P.n)) (A : Adversary P.n Msg St)
    (c : Config P.n Msg St A.σ) : PMF (Config P.n Msg St A.σ) :=
  (moves S (Pi.next P) P.t A.step (P.n * Pi.opCap P + P.n + P.t + 1)
    { c with
      budget := fun _ => Pi.opCap P
      yielded := fun _ => false }).bind (boundary (Pi.electAt P c.round) E)

/-- `k` further rounds, from any configuration. Started from a configuration in the support of a
prefix, this is the conditional law of the continuation, since the configuration holds all history. -/
noncomputable def runRounds (Pi : Protocol Msg St) (S : Sig) (P : Params)
    (E : List (Event P.n Msg St) → PMF (Fin P.n)) (A : Adversary P.n Msg St) :
    ℕ → Config P.n Msg St A.σ → PMF (Config P.n Msg St A.σ)
  | 0, c => PMF.pure c
  | k + 1, c => (oneRound Pi S P E A c).bind (runRounds Pi S P E A k)

/-- The local computation after the last boundary: each active uncorrupted player, in identity order,
processes what the last boundary delivered and may decide; no transmission is possible. This is the
"public final deadline" at which "an undecided player outputs the fixed fallback bit" (p.30), and the
moment of the output of dissemination ("At the delivery boundary it outputs", p.26). -/
noncomputable def finalize (Pi : Protocol Msg St) (S : Sig) (P : Params)
    (c : Config P.n Msg St σ) : PMF (Config P.n Msg St σ) :=
  (List.finRange P.n).foldl
    (fun d i =>
      d.bind fun c =>
        if i ∉ c.corrupted ∧ c.active i = true then c.activate S (Pi.next P) true i (Pi.opCap P)
        else PMF.pure c)
    (PMF.pure c)

/-- The execution from a configuration through the public cap. -/
noncomputable def execFrom (Pi : Protocol Msg St) (S : Sig) (P : Params)
    (E : List (Event P.n Msg St) → PMF (Fin P.n)) (A : Adversary P.n Msg St)
    (c : Config P.n Msg St A.σ) : PMF (Config P.n Msg St A.σ) :=
  (runRounds Pi S P E A (Pi.roundCap P - c.round) c).bind (finalize Pi S P)

/-- The setup: keys by honest key generation, the adversary's initial state, nobody corrupted, and the
public keys as the first observation. -/
noncomputable def setup (Pi : Protocol Msg St) (S : Sig) (P : Params) (x : Bool)
    (A : Adversary P.n Msg St) : PMF (Config P.n Msg St A.σ) :=
  (S.keysLaw P.n).bind fun ks =>
    A.init.map fun a =>
      (Config.start Pi P x ks.1 ks.2 ∅ [] a []).push (Obs.keys ks.1)

/-- The whole execution of protocol `Pi` under scheme `S`, parameters `P`, sender input `x`, election law `E` and
adversary `A` (§4.3, p.13: "setup randomness, private protocol randomness, and the adversary's
randomness"). -/
noncomputable def exec (Pi : Protocol Msg St) (S : Sig) (P : Params) (x : Bool)
    (E : List (Event P.n Msg St) → PMF (Fin P.n)) (A : Adversary P.n Msg St) :
    PMF (Config P.n Msg St A.σ) :=
  (setup Pi S P x A).bind (execFrom Pi S P E A)

/-- The ideal election of §4.3, p.13: "an independent uniform identity", whatever the transcript. -/
noncomputable def uniformElect (P : Params) {Msg St : Type} :
    List (Event P.n Msg St) → PMF (Fin P.n) :=
  fun _ => PMF.uniformOfFintype _

/-- An election law at statistical distance at most `ζ` from uniform, conditional on every transcript
(§5.1, p.14: "A statistical distance ζ from the uniform distribution can be allowed"). -/
def ElectNear (P : Params) {Msg St : Type} (ζ : ℝ) (E : List (Event P.n Msg St) → PMF (Fin P.n)) :
    Prop :=
  ∀ (h : List (Event P.n Msg St)) (U : Set (Fin P.n)),
    ((E h).toOuterMeasure U).toReal ≤ (U.ncard : ℝ) / P.n + ζ

end BeyondDS


