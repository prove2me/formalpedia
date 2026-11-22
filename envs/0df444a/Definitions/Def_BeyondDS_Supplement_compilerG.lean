-- Prove2me | Definitions.Def_BeyondDS_Supplement_compilerG
-- name    : BeyondDS_Supplement_compilerG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:09:31.851804+00:00
-- url     : https://prove2.me/theorems/6f9bf972-1ff6-4088-bcaa-04f4c9f288a3
-- title:
--   The compiler of §5 with an arbitrary dissemination implementation and an arbitrary termination procedure
-- statement:
--   This is the protocol of Theorem 6: the compiler from dissemination to Byzantine broadcast of §5.2, with its two components left as parameters.
--
--   **Dissemination implementation.** An implementation has a duration $d\ge1$ in rounds. In each of its $d$ rounds it runs an arbitrary local program that may sign, verify, sample and send; it keeps its own memory between rounds. At the deadline it returns a set of payloads computed from its memory and the last deliveries, and the compiler keeps those that carry a verifying source signature for this invocation. An implementation cannot end a round, decide, halt or overwrite the compiler's state. Its guarantees are not part of the definition; they are the hypotheses of Theorem 6.
--
--   **Termination procedure.** At any deadline, an undecided player holding a verifying termination certificate decides its bit. The termination procedure is the rule that says, at the beginning of each call, whether a decided player may halt. Until it may, the player continues the ordinary stage actions and adds its termination evidence to each frozen source payload.
--
--   **Protocol.** There are $Q=6J+3$ calls: one initialization call, six calls (Status, Prepare-1, Prepare-2, Proposal, Vote, Commit) for each of $J$ main iterations, and two forwarding calls. In each call a player performs the stage action of the base mission, signs and freezes its payload, runs one dissemination invocation, and at the deadline extracts the evidence records, updates its state and decides if it now holds a termination certificate. The election output of iteration $r$ is revealed at the last boundary of its Proposal call. The public final deadline is the end of round $d(6J+3)$; there every remaining player stops and an undecided player decides the fallback bit $0$.
--
--   The evidence records, certificates and stage actions are those of the published compiler of the base mission. The differences from it are that dissemination and termination are parameters, that a certificate holder keeps performing ordinary stage actions, and that there are two forwarding calls instead of three.
--
--   **Formalization Note** Messages are the envelopes of the base mission; their signature fields carry arbitrary bit strings, so any message format can be coded. `quiet` runs a component's program with its `yield`, `decide` and `halt` operations and its notes removed, and `OpsLE` bounds the number of operations of a program, which the well-formedness condition `Dissem.WF` uses.
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.1, p.14 (PDF p.15); §5.2, pp.14–16 (PDF pp.15–17); Theorem 6, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS.Supplement

open BeyondDS

/-- Run a program as a local computation inside one sending interval: its `yield`, `decide` and `halt`
operations and its notes are dropped (each is answered `done`), so that a component cannot end a round, decide,
halt or overwrite the readable state. Signing, verification, sampling and sends are kept. -/
def quiet {Msg V α : Type} : Prog Msg V α → Prog Msg V α
  | Prog.ret a => Prog.ret a
  | Prog.op o k =>
    match o with
    | Op.yield => quiet (k Resp.done)
    | Op.decide _ => quiet (k Resp.done)
    | Op.halt => quiet (k Resp.done)
    | o => Prog.op o fun r => quiet (k r)
  | Prog.note _ k => quiet k

/-- A program uses at most `N` operations, whatever the answers. -/
inductive OpsLE {Msg V α : Type} : ℕ → Prog Msg V α → Prop
  | ret (N : ℕ) (a : α) : OpsLE N (Prog.ret a)
  | op (N : ℕ) (o : Op Msg) (k : Resp Msg → Prog Msg V α) : (∀ r, OpsLE N (k r)) → OpsLE (N + 1) (Prog.op o k)
  | note (N : ℕ) (v : V) (k : Prog Msg V α) : OpsLE N k → OpsLE N (Prog.note v k)

/-- An all-to-all dissemination implementation, as a component of the compiler of Rambaud, *Beyond Dolev–Strong*,
STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.1, p.14 (PDF 15): "An all-to-all dissemination invocation
gives each participating player i one frozen, signed payload M_i and returns a set of authenticated payloads to
each recipient at a public deadline. […] The invocation has fixed duration d".

* `d`: the duration, in rounds. `opCap`: a bound on the operations of one sending interval.
* `step cfg r inbox st`: the sending interval of round `r ∈ {1, …, d}` of the invocation described by `cfg`
  (population, budget, invocation label `cfg.sid`, own identity `cfg.self`), given what the previous round
  delivered (`[]` for `r = 1`). The player's frozen source payload is `st.pay` at `r = 1` and is recorded in its
  current call record. The step may sign, verify, sample and send; it returns the state, of which only the two
  buffers `pay` and `ack` are kept, as the implementation's memory.
* `out cfg st inbox`: the payloads returned at the deadline, from the memory and the last round's deliveries.
  The compiler keeps those with a verifying source signature for this invocation.

**Formalization Note.** Messages are the envelopes of the base mission, which carry arbitrary bit strings in
their signature fields, so any message format can be coded; the implementation is otherwise an arbitrary
program. Its guarantees (delivery, error, cost) are not part of this structure: they are hypotheses of
Theorem 6. -/
structure Dissem where
  d : ℕ
  opCap : ℕ
  step : CallCfg (List EvRec) → ℕ → List (ℕ × CMsg) → LS (List EvRec) → PM (List EvRec) (LS (List EvRec))
  out : CallCfg (List EvRec) → LS (List EvRec) → List (ℕ × CMsg) → List (Payload (List EvRec))

/-- The implementation is well formed: it lasts at least one round and each sending interval stays within its
declared number of operations. -/
def Dissem.WF (D : Dissem) : Prop :=
  1 ≤ D.d ∧ ∀ cfg r inbox st, OpsLE D.opCap (quiet (D.step cfg r inbox st))

/-- A termination procedure in the sense of §5.2, p.16: "At any deadline, an undecided player holding a verifying
termination certificate decides its bit and invokes the termination procedure. Until that procedure permits it to
halt, it continues the ordinary stage actions and also includes its termination certificate in each frozen source
payload." The procedure is the rule that permits halting: `H cfg c st` says whether a decided player with readable
state `st` halts at the beginning of call `c`. -/
abbrev HaltRule := CallCfg (List EvRec) → ℕ → LS (List EvRec) → Bool

/-- One dissemination invocation run by a player: a call record is opened with the frozen source payload; in each
of the `d` rounds the implementation's sending interval runs and the round ends; at the deadline the returned
payloads with a verifying source signature and this invocation's label become the player's payload buffer, and the
record's output. The readable state is saved before each round ends. An election output delivered with the last
boundary is recorded (`cfg.iter` is the iteration it belongs to). -/
def callG (D : Dissem) (cfg : CallCfg (List EvRec)) (c : ℕ) (terminal : Bool)
    (source : Option (Payload (List EvRec))) (st : LS (List EvRec)) : PM (List EvRec) (LS (List EvRec)) := do
  let st : LS (List EvRec) := { st with
    calls := ⟨c, terminal, source, LS.buf cfg st, none, none, none, none, none⟩ :: st.calls }
  Prog.save st
  let init : LS (List EvRec) × List (ℕ × CMsg) × Option ℕ := (st, [], none)
  let fin ← (List.range D.d).foldlM
    (fun (s : LS (List EvRec) × List (ℕ × CMsg) × Option ℕ) r => do
      let st' ← quiet (D.step cfg (r + 1) s.2.1 s.1)
      let st : LS (List EvRec) := { s.1 with pay := st'.pay, ack := st'.ack }
      Prog.save st
      let (inbox, e) ← Prog.yield
      pure (st, inbox, e)) init
  let st := fin.1
  let cand := ((D.out cfg st fin.2.1).filter fun p => decide (p.sid = c)).dedup
  let vs ← Prog.verifyAll (cand.map (payQuery cfg))
  let st : LS (List EvRec) := { st with pay := keepOK cand vs }
  let st := match fin.2.2, cfg.iter with
    | some l, some it => { st with elect := st.elect ++ [(it, l)] }
    | _, _ => st
  let st := st.snap fun r => { r with output := some (LS.buf cfg st) }
  pure st

/-- One call of the compiler with a dissemination implementation `D` and a termination procedure `H` (§5.2,
pp.14–16). At the call's beginning a player that holds a verifying termination certificate has decided; a decided
player halts if the procedure permits it. Otherwise it performs the ordinary stage action of the base mission
(`BeyondDS.stageItems`), adds its termination evidence to the payload if it holds any, signs and freezes the
payload, runs the invocation, and at the deadline extracts the evidence, updates its state and decides if it now
holds a termination certificate (`BeyondDS.closeCall`). The second component of the result says that the player
has halted. -/
def compilerCallG (D : Dissem) (H : HaltRule) (cfg₀ : CallCfg (List EvRec)) (input : Option Bool)
    (s : LS (List EvRec) × Bool) (c : ℕ) : PM (List EvRec) (LS (List EvRec) × Bool) := do
  if s.2 then pure s
  else
    let stage := stageOf cfg₀.J c
    let cfg := { cfg₀ with sid := c, iter := electIter cfg₀.J c }
    let st ← maybeDecide cfg s.1
    if st.decided.isSome && H cfg c st then
      Prog.halt
      pure (st, true)
    else
      let terminal := (firstTerm (cfg.ctx st) st.store).isSome
      let st : LS (List EvRec) := { st with pay := [], ack := [] }
      let st : LS (List EvRec) := match stage with
        | Stage.status r => { st with frozen := (r, st.rank, st.bit) :: st.frozen }
        | _ => st
      let (items, st) ← stageItems cfg input st stage
      let body := items ++ (if terminal then termEvidence (cfg.ctx st) st.store else [])
      let ss ← Prog.signAll [encDatum cfg.enc (Datum.payload c cfg.self body)]
      let p : Payload (List EvRec) := ⟨c, cfg.self, body, ss.headD []⟩
      let st ← callG D cfg c terminal (some p) { st with pay := [p] }
      let st ← closeCall cfg st stage
      pure (st, false)

/-- The whole program of player `i` (Theorem 6, p.18): the initialization call, `J` main iterations of six calls
and two forwarding calls, `6J + 3` calls in all; then the public final deadline, where "every remaining player
[stops], assigning a fixed fallback bit to an undecided player". -/
def compilerProgG (D : Dissem) (H : HaltRule) (n t J sender i : ℕ) (input : Option Bool) :
    PM (List EvRec) Unit := do
  let cfg : CallCfg (List EvRec) := ⟨n, t, 0, 0, 0, i, sender, J, none, true, encRecs⟩
  let init : LS (List EvRec) × Bool := ({}, false)
  let last ← (List.range (6 * J + 3)).foldlM (compilerCallG D H cfg input) init
  match last.1.decided with
  | some _ => pure ()
  | none =>
    Prog.decide false
    Prog.save { last.1 with decided := some false }

/-- The election schedule: the output of iteration `r` is revealed at the last boundary of its Proposal call,
call `6r − 2`, that is at the boundary of round `d(6r − 1) − 1`, counted from `0` (§5.1, p.14: "the oracle returns
one common index L_r […] only after that iteration's Proposal deadline"). -/
def electAtG (d J R : ℕ) : Bool :=
  decide (0 < d ∧ (R + 1) % d = 0 ∧ ((R + 1) / d + 1) % 6 = 0 ∧ 1 ≤ ((R + 1) / d + 1) / 6 ∧
    ((R + 1) / d + 1) / 6 ≤ J)

/-- The compiler of §5 with an arbitrary dissemination implementation `D`, an arbitrary termination procedure `H`,
`J` main iterations and two forwarding calls (Theorem 6, p.18). The public final deadline is the end of round
`d(6J + 3)`.

**Formalization Note.** The evidence records, their verification, the stage actions and the deadline updates are
those of the base mission (`BeyondDS.stageItems`, `BeyondDS.closeCall`, `BeyondDS.certValid`); what differs from
`BeyondDS.compiler` is that dissemination and termination are parameters, a certificate holder keeps performing
ordinary stage actions, and there are two forwarding calls. -/
def compilerG (D : Dissem) (H : HaltRule) (J : ℕ) : Protocol CMsg CSt :=
  Protocol.ofProg {} (fun P i x => compilerProgG D H P.n P.t J P.sender.val i.val x)
    (fun _ => D.d * (6 * J + 3)) (fun _ => D.opCap + 16) (fun _ R => electAtG D.d J R)

end BeyondDS.Supplement


