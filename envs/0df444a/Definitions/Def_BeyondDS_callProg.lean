-- Prove2me | Definitions.Def_BeyondDS_callProg
-- name    : BeyondDS_callProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:57.589233+00:00
-- url     : https://prove2.me/theorems/a9fc27c5-152d-497b-964b-49f99a23a9fb
-- title:
--   The seven-round adaptive dissemination protocol of §7.4
-- statement:
--   With $\lambda\ge1024\log(n+1)$ and (19)
--
--   $$K=\lceil\sqrt{n\lambda}\,\rceil,\qquad B=\min\{n,\lceil 512n/K\rceil\},$$
--
--   one dissemination call of a player runs seven rounds. A random trial samples a destination uniformly from $[n]$ immediately before sending. In the sparse case $K<n$:
--
--   1. Round 1: $K$ trials carrying its initial payload buffer.
--   2. Round 2: $K$ trials carrying its full payload buffer as held at the beginning of the round.
--   3. Round 3: it signs an acknowledgement of every accepted payload held at the end of round 2, adds them to its acknowledgement buffer, freezes it and performs $K$ trials carrying it.
--   4. Round 4: $K$ trials carrying its full acknowledgement buffer.
--   5. Round 5: a source with $A_i$ the distinct issuers of accepted acknowledgements of its exact payload sets $d_i=\max\{0,t+1-|A_i|\}$; if $d_i\le B$ it sends $P_i$ to the first $d_i$ identities outside $A_i$ in increasing order, else to every other identity.
--   6. Rounds 6–7: $K$ trials carrying its full payload buffer; it outputs its retained accepted payloads after the last boundary.
--
--   In the dense case $K\ge n$ each source sends its payload to every other identity in round 1 and players retain what they receive through round 7. Recipients process only the record type of the round, check instance, round and signatures, ignore duplicates and retain all verifying records; an accepted acknowledgement also adds its payload. With the terminal switch on, the changes of §8.1 apply: termination evidence is forwarded in payload rounds, terminal acknowledgements are signed before round 3 and forwarded in rounds 3–4, a terminal source counts terminal acknowledgers of its decided bit in round 5 and sends its termination certificate, and a player in its grace call halts after its round-2 sends. Each player records snapshots of its buffers after rounds 2, 3 (frozen), 4, 5 and 7 for the statements of the mission. The stand-alone protocol `dissem` runs one call with no election.
--
--   **Formalization Note** $d_i$ uses truncated subtraction, which is exactly $\max\{0,\cdot\}$. The per-round operation cap is $2K+2n+64$.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §7.1, p.22 (PDF p.23); §7.4, pp.26–27 (PDF pp.27–28), eq. (19); §8.1, pp.29–30 (PDF pp.30–31)

import Mathlib
import Definitions.Def_BeyondDS_Prog
import Definitions.Def_BeyondDS_certValid

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- A snapshot of a player's buffers: payload records, acknowledgement records, the evidence it would forward, and its whole
evidence store. -/
structure Buf (B : Type) where
  pay : List (Payload B)
  ack : List (Ack B)
  term : List EvRec
  store : List EvRec

/-- What a player records about one seven-round call, for the statements of the mission. Each buffer snapshot is
taken once the player has processed that round's boundary.

* `terminal`: the call began in terminal mode. `source`: the frozen source payload, if any.
* `frozen1`: the initial buffer. `after2`: the buffer after round 2. `frozen3`: the frozen acknowledgement buffer.
* `after4`: the acknowledgement buffer after round 4. `after5`: the buffer after round 5, the "recovery" prefix.
* `output`: the buffer after round 7. -/
structure CallRec (B : Type) where
  call : ℕ
  terminal : Bool
  source : Option (Payload B)
  frozen1 : Buf B
  after2 : Option (Buf B)
  frozen3 : Option (Buf B)
  after4 : Option (Buf B)
  after5 : Option (Buf B)
  output : Option (Buf B)

/-- The readable part of a player's local state in dissemination and in the compiler.

* `pay`, `ack`: the buffers of the current call (§7.4, p.26). `store`: the verified elementary evidence (§5.2, p.15).
* `elect`: election outputs `(r, L_r)` so far.
* `bit`, `rank`: "The current state of a player consists of a bit and a highest-rank certificate it has accepted"
  (p.14); rank `−1` is the fallback.
* `frozen`: the triples `(r, h^r_i, bit)`, the state frozen at the Status stage of iteration `r`. `ownHeader`: the headers it signed as a candidate.
* `decided`: its decision. `calls`: its call records, newest first. -/
structure LS (B : Type) where
  pay : List (Payload B) := []
  ack : List (Ack B) := []
  store : List EvRec := []
  elect : List (ℕ × ℕ) := []
  bit : Bool := false
  rank : ℤ := -1
  frozen : List (ℕ × ℤ × Bool) := []
  ownHeader : List Header := []
  decided : Option Bool := none
  calls : List (CallRec B) := []

/-- The public data of one call. `K` and `Bd` are `K`, `B` of (19), p.26. `iter` is the iteration of a call whose last
boundary may reveal an election. `useTerm` switches on the terminal rules of §8.1; off, this is the plain protocol of
§7.4. `enc` codes payload bodies for signing. -/
structure CallCfg (B : Type) where
  n : ℕ
  t : ℕ
  K : ℕ
  Bd : ℕ
  sid : ℕ
  self : ℕ
  sender : ℕ
  J : ℕ
  iter : Option ℕ
  useTerm : Bool
  enc : B → Str

variable {B : Type} [DecidableEq B]

/-- The programs of dissemination and of the compiler. -/
abbrev PM (B : Type) := Prog (Envelope B) (LS B)

/-- The evidence context of a player. -/
def CallCfg.ctx (cfg : CallCfg B) (st : LS B) : EvCtx :=
  ⟨cfg.n, cfg.t, cfg.sender, cfg.J, st.elect⟩

/-- Keep the elements whose verdict is `true`. -/
def keepOK {α : Type} (l : List α) (vs : List Bool) : List α :=
  ((l.zip vs).filter Prod.snd).map Prod.fst

/-- Update the record of the current call. -/
def LS.snap (st : LS B) (f : CallRec B → CallRec B) : LS B :=
  { st with
    calls := match st.calls with
      | [] => []
      | r :: rs => f r :: rs }

/-- The buffers of a player, as a snapshot. -/
def LS.buf (cfg : CallCfg B) (st : LS B) : Buf B :=
  ⟨st.pay, st.ack, if cfg.useTerm then termEvidence (cfg.ctx st) st.store else [], st.store⟩

/-- Check elementary evidence: "All signatures are checked individually" after the domain checks (p.15), and retain
what verifies. -/
def absorbEv (cfg : CallCfg B) (st : LS B) (es : List EvRec) : PM B (LS B) := do
  let x := cfg.ctx st
  let new := (es.filter fun e => e.inDomain x && decide (e ∉ st.store)).dedup
  let vs ← Prog.verifyAll (new.map (EvRec.query cfg.enc x))
  pure { st with store := st.store ++ keepOK new vs }

/-- On first obtaining a verifying termination certificate, decide its bit (§8.1, p.29). -/
def maybeDecide (cfg : CallCfg B) (st : LS B) : PM B (LS B) := do
  if cfg.useTerm && st.decided.isNone then
    match firstTerm (cfg.ctx st) st.store with
    | some (_, b) =>
      Prog.decide b
      let st' := { st with decided := some b }
      Prog.save st'
      pure st'
    | none => pure st
  else pure st

/-- The verification query of a payload record. -/
def payQuery (cfg : CallCfg B) (p : Payload B) : ℕ × Str × Str :=
  (p.src, encDatum cfg.enc (Datum.payload p.sid p.src p.body), p.sig)

/-- The verification query of an acknowledgement's own signature. -/
def ackQuery (cfg : CallCfg B) (a : Ack B) : ℕ × Str × Str :=
  (a.issuer, encDatum cfg.enc (Datum.ack cfg.sid a.issuer a.payload), a.sig)

/-- Process what round `r` delivered: "Recipients process only the designated record type for that round; malformed
envelopes, mismatched instance or round labels, and messages arriving after the round's delivery boundary are ignored"
(p.26). Rounds 3 and 4 carry acknowledgement records, and "Receiving an accepted acknowledgement also adds its enclosed
payload to the payload buffer". Duplicates are ignored and all verifying records are retained, "including conflicting
payloads from one source" (p.22). -/
def absorbRound (cfg : CallCfg B) (r : ℕ) (inbox : List (ℕ × Envelope B)) (st : LS B) : PM B (LS B) := do
  let envs := (inbox.map Prod.snd).filter fun e => decide (e.sid = cfg.sid ∧ e.round = r)
  let st ←
    if r = 3 ∨ r = 4 then do
      let as := (envs.flatMap Envelope.ack).filter fun a => decide (a.payload.sid = cfg.sid ∧ a ∉ st.ack)
      let vs ← Prog.verifyAll (as.map (ackQuery cfg))
      let ws ← Prog.verifyAll (as.map fun a => payQuery cfg a.payload)
      let good := keepOK as (vs.zipWith and ws)
      pure { st with
        ack := st.ack ++ good.dedup
        pay := st.pay ++ ((good.map Ack.payload).dedup.filter fun p => decide (p ∉ st.pay)) }
    else do
      let ps := ((envs.flatMap Envelope.pay).filter fun p => decide (p.sid = cfg.sid ∧ p ∉ st.pay)).dedup
      let vs ← Prog.verifyAll (ps.map (payQuery cfg))
      pure { st with pay := st.pay ++ keepOK ps vs }
  let ts := envs.flatMap Envelope.term
  let st ←
    if cfg.useTerm then
      absorbEv cfg st (if r = 3 ∨ r = 4 then tacks ts else ts)
    else pure st
  let st ← maybeDecide cfg st
  Prog.save st
  pure st

/-- End the round: yield, note an election output, and process the deliveries. -/
def endRound (cfg : CallCfg B) (r : ℕ) (st : LS B) : PM B (LS B) := do
  let (inbox, e) ← Prog.yield
  let st := match e, cfg.iter with
    | some l, some it => { st with elect := st.elect ++ [(it, l)] }
    | _, _ => st
  absorbRound cfg r inbox st

/-- `K` random transmission trials carrying a frozen message: "A random transmission trial chooses a destination
uniformly from [n], using fresh private randomness immediately before transmission" (p.22). -/
def trials (cfg : CallCfg B) (m : Envelope B) : PM B Unit := do
  for _ in List.range cfg.K do
    let j ← Prog.sample (cfg.n - 1)
    Prog.send j m

/-- A payload-round message: the full payload buffer and the termination evidence. -/
def payEnv (cfg : CallCfg B) (r : ℕ) (st : LS B) : Envelope B :=
  ⟨cfg.sid, r, st.pay, [], if cfg.useTerm then termEvidence (cfg.ctx st) st.store else []⟩

/-- An acknowledgement-round message: the acknowledgement buffer and the terminal acknowledgements. -/
def ackEnv (cfg : CallCfg B) (r : ℕ) (st : LS B) : Envelope B :=
  ⟨cfg.sid, r, [], st.ack, if cfg.useTerm then tacks st.store else []⟩

/-- Before round 3: "each player signs an acknowledgement for every accepted payload held at the end of round 2, adds these
records to its acknowledgement buffer, and freezes that buffer" (p.26); and "every holder of termination evidence signs its
terminal acknowledgement" (p.29), for "every bit for which it holds verifying termination evidence". -/
def signAcks (cfg : CallCfg B) (st : LS B) : PM B (LS B) := do
  let ss ← Prog.signAll (st.pay.map fun p => encDatum cfg.enc (Datum.ack cfg.sid cfg.self p))
  let own : List (Ack B) := (st.pay.zip ss).map fun e => ⟨cfg.self, e.1, e.2⟩
  let st := { st with ack := st.ack ++ own.filter fun a => decide (a ∉ st.ack) }
  if cfg.useTerm then
    let x := cfg.ctx st
    let bits := (termBits x st.store).filter fun b =>
      !(st.store.any fun e =>
        match e with
        | EvRec.tack b' j _ => b' == b && decide (j = cfg.self)
        | _ => false)
    let ts ← Prog.signAll (bits.map fun b => encDatum cfg.enc (Datum.tack cfg.self b))
    pure { st with store := st.store ++ (bits.zip ts).map fun e => EvRec.tack e.1 cfg.self e.2 }
  else pure st

/-- The destinations of a recovery step (§7.4, p.26): with witness set `A`, the deficit is `d = max{0, t + 1 − |A|}`, and here
truncated subtraction is exactly that. "If di ≤ B, it sends Pi to the first di identities in increasing identity order outside
Ai. […] If di > B, it sends Pi to every other identity". -/
def recoveryTargets (cfg : CallCfg B) (A : List ℕ) : List ℕ :=
  let d := (cfg.t + 1) - A.dedup.length
  if d ≤ cfg.Bd then ((List.range cfg.n).filter fun j => j ∉ A).take d
  else (List.range cfg.n).filter fun j => j ≠ cfg.self

/-- Round 5. An ordinary source counts the distinct issuers of accepted acknowledgements "for its exact initial payload". A source
that began the call in terminal mode counts "distinct terminal acknowledgers for its decided bit" and sends its termination
certificate (§8.1, p.30). -/
def recovery (cfg : CallCfg B) (terminal : Bool) (st : LS B) : PM B Unit := do
  if terminal then
    let x := cfg.ctx st
    match st.decided with
    | some b =>
      match (rankBits cfg.J).find? (fun e => e.2 == b && termValid x st.store e.1 b) with
      | some (r, _) =>
        let A := st.store.filterMap fun e =>
          match e with
          | EvRec.tack b₂ j _ => if b₂ = b then some j else none
          | _ => none
        for j in recoveryTargets cfg A do
          Prog.send j ⟨cfg.sid, 5, [], [], termClosure x st.store r b⟩
      | none => pure ()
    | none => pure ()
  else
    match st.calls.head?.bind CallRec.source with
    | some p =>
      let A := (st.ack.filter fun a => decide (a.payload = p)).map Ack.issuer
      for j in recoveryTargets cfg A do
        Prog.send j ⟨cfg.sid, 5, [p], [], []⟩
    | none => pure ()

/-- The seven rounds of the sparse case `K < n` (§7.4, p.26; with the changes of §8.1, pp.29–30 when `useTerm`). If `grace`, the
player halts after its sends of round 2 (§8.1, p.30: "it participates through rounds 1–2 of the following call and then halts"). -/
def sparseCall (cfg : CallCfg B) (terminal grace : Bool) (st : LS B) : PM B (LS B) := do
  trials cfg (payEnv cfg 1 st)
  let st ← endRound cfg 1 st
  trials cfg (payEnv cfg 2 st)
  if grace then
    Prog.halt
    pure st
  else
    let st ← endRound cfg 2 st
    let st := st.snap fun r => { r with after2 := some (LS.buf cfg st) }
    Prog.save st
    let st ← signAcks cfg st
    let st := st.snap fun r => { r with frozen3 := some (LS.buf cfg st) }
    Prog.save st
    trials cfg (ackEnv cfg 3 st)
    let st ← endRound cfg 3 st
    trials cfg (ackEnv cfg 4 st)
    let st ← endRound cfg 4 st
    let st := st.snap fun r => { r with after4 := some (LS.buf cfg st) }
    Prog.save st
    recovery cfg terminal st
    let st ← endRound cfg 5 st
    let st := st.snap fun r => { r with after5 := some (LS.buf cfg st) }
    Prog.save st
    trials cfg (payEnv cfg 6 st)
    let st ← endRound cfg 6 st
    trials cfg (payEnv cfg 7 st)
    let st ← endRound cfg 7 st
    let st := st.snap fun r => { r with output := some (LS.buf cfg st) }
    Prog.save st
    pure st

/-- The seven rounds of the dense case `K ≥ n`: "each source sends its signed payload directly to every other identity in round 1, and all
players retain received payloads through round 7 without further transmissions" (p.26); "every active source directly sends its frozen
ordinary payload or terminal evidence to all identities in round 1" (p.30). -/
def denseCall (cfg : CallCfg B) (grace : Bool) (st : LS B) : PM B (LS B) := do
  for j in (List.range cfg.n).filter (fun j => j ≠ cfg.self) do
    Prog.send j (payEnv cfg 1 st)
  let st ← endRound cfg 1 st
  if grace then
    Prog.halt
    pure st
  else
    let st ← endRound cfg 2 st
    let st := st.snap fun r => { r with after2 := some (LS.buf cfg st) }
    let st := st.snap fun r => { r with frozen3 := some (LS.buf cfg st) }
    let st ← endRound cfg 3 st
    let st ← endRound cfg 4 st
    let st := st.snap fun r => { r with after4 := some (LS.buf cfg st) }
    let st ← endRound cfg 5 st
    let st := st.snap fun r => { r with after5 := some (LS.buf cfg st) }
    let st ← endRound cfg 6 st
    let st ← endRound cfg 7 st
    let st := st.snap fun r => { r with output := some (LS.buf cfg st) }
    Prog.save st
    pure st

/-- One seven-round call, from buffers frozen by the caller. A new call record is opened with the frozen initial buffer. -/
def callProg (cfg : CallCfg B) (call : ℕ) (terminal grace : Bool) (source : Option (Payload B)) (st : LS B) :
    PM B (LS B) := do
  let st : LS B := { st with
    calls := ⟨call, terminal, source, LS.buf cfg st, none, none, none, none, none⟩ :: st.calls }
  Prog.save st
  if cfg.K < cfg.n then sparseCall cfg terminal grace st else denseCall cfg grace st

/-- `K = ⌈√(nλ)⌉` of (19), p.26. -/
noncomputable def paramK (P : Params) : ℕ := ⌈Real.sqrt ((P.n : ℝ) * P.lam)⌉₊

/-- `B = min{n, ⌈512n/K⌉}` of (19), p.26. -/
noncomputable def paramB (P : Params) : ℕ := min P.n ⌈512 * (P.n : ℝ) / (paramK P)⌉₊

/-- The stand-alone dissemination program of source `i` with input string `x` (§7.1, §7.4). -/
def dissemProg (n t K Bd sid : ℕ) (i : ℕ) (x : Str) : PM Str Unit := do
  let cfg : CallCfg Str := ⟨n, t, K, Bd, sid, i, 0, 0, none, false, id⟩
  let ss ← Prog.signAll [encDatum id (Datum.payload sid i x)]
  let p : Payload Str := ⟨sid, i, x, ss.headD []⟩
  let _ ← callProg cfg sid false false (some p) { pay := [p] }

/-- The per-round operation cap of the protocols of this mission: at most `2K` operations for the trials or `n` sends for a
recovery or a direct sending, plus a constant number of batches and bookkeeping operations. -/
noncomputable def missionOpCap (P : Params) : ℕ := 2 * paramK P + 2 * P.n + 64

/-- The all-to-all dissemination protocol of §7.4, pp.26–27 for inputs `x` and instance `sid`, with parameters (19). "A round consists
of a sending interval followed by a delivery boundary" (p.22). The protocol has seven rounds and no election. Its output is the player's
buffer after the local step following the last boundary. -/
noncomputable def dissem (sid : ℕ) (x : (P : Params) → Fin P.n → Str) : Protocol (Envelope Str) (ProgState (Envelope Str) (LS Str)) :=
  Protocol.ofProg {} (fun P i _ => dissemProg P.n P.t (paramK P) (paramB P) sid i.val (x P i))
    (fun _ => 7) missionOpCap (fun _ _ => false)

end BeyondDS


