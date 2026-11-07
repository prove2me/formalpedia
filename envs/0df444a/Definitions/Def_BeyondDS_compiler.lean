-- Prove2me | Definitions.Def_BeyondDS_compiler
-- name    : BeyondDS_compiler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:11:03.60841+00:00
-- url     : https://prove2.me/theorems/030df9f7-77d0-4d30-a926-49a6af619f02
-- title:
--   The compiler from dissemination to Byzantine broadcast, with the terminal procedure
-- statement:
--   The compiler with iteration cap $J$ runs $Q=6J+4$ seven-round dissemination calls: initialization, then for each iteration $r=1,\dots,J$ the six stages Status, Prepare-1, Prepare-2, Proposal, Vote, Commit, then three forwarding calls with empty ordinary payloads. The election output $L_r$ is revealed at the last boundary of iteration $r$'s Proposal call.
--
--   1. **Initialization.** The sender signs its bit; every player then takes state (bit, rank) $=(b,0)$ for a received sender signature on $b$ (bit $0$ first if both arrive), else $(0,-1)$.
--   2. **Status.** A player freezes $h^r_i$ (its rank) and disseminates its state with its evidence.
--   3. **Prepare-1.** Each candidate signs the header $(r,i,b,k)$ of a maximum-rank verifying state among its own and those received (ties: bit 0) and disseminates it with its support.
--   4. **Prepare-2.** For each candidate with a verifying header and evidence, the player endorses exactly one, chosen by the fixed ordering (higher rank, then bit 0).
--   5. **Proposal.** A candidate with $t+1$ endorsements disseminates its prepared proposal.
--   6. **Vote.** If it holds a prepared proposal of $L_r$ with support rank $\ge h^r_i$, it votes for one chosen by the fixed ordering, attaching it.
--   7. **Commit.** It commits to $b$ if it has a verifying iteration-$r$ certificate for $b$ and no verifying iteration-$r$ vote for $1-b$; at the deadline it accepts every higher-rank certificate carried by a commit.
--
--   **Terminal procedure** (§8.1). On first holding a termination certificate a player decides its bit. At each call boundary it first fixes its mode; a terminal source signs terminal acknowledgements of each bit with verifying termination evidence and supplies termination evidence instead of a stage payload. After completing a qualifying call (one begun with a termination certificate) it takes part in rounds 1–2 of the next call and halts. At the end of the third forwarding call an undecided player outputs $0$. After every call a player extracts the elementary evidence of retained payloads. The round cap is $7Q$.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §5.2, pp.14–16 (PDF pp.15–17); §8, pp.29–30 (PDF pp.30–31); eq. (32), p.33 (PDF p.34)

import Mathlib
import Definitions.Def_BeyondDS_callProg

set_option autoImplicit false

open QAlgorithms.Complexity

namespace BeyondDS

/-- The stage of a scheduled call of the compiler: initialization (call `0`), the six stages of iteration `r` (§5.2, p.16: "Six calls per
iteration"; Elect is not a call), or a forwarding call (§8.1, p.30). There are `Q = 6J + 4` calls. -/
inductive Stage where
  | init
  | status (r : ℕ)
  | prepare1 (r : ℕ)
  | prepare2 (r : ℕ)
  | proposal (r : ℕ)
  | vote (r : ℕ)
  | commit (r : ℕ)
  | forward

/-- The stage of call `c`. -/
def stageOf (J c : ℕ) : Stage :=
  if c = 0 then Stage.init
  else if c ≤ 6 * J then
    let r := (c - 1) / 6 + 1
    match (c - 1) % 6 with
    | 0 => Stage.status r
    | 1 => Stage.prepare1 r
    | 2 => Stage.prepare2 r
    | 3 => Stage.proposal r
    | 4 => Stage.vote r
    | _ => Stage.commit r
  else Stage.forward

/-- The call at whose last boundary an election output appears: the Proposal call of iteration `r`. -/
def electIter (J c : ℕ) : Option ℕ :=
  match stageOf J c with
  | Stage.proposal r => some r
  | _ => none

/-- The election schedule: "The election is revealed only after all four of these stages have ended" (p.15). The Proposal call of iteration
`r` is call `6r − 2`, whose last round is `7(6r − 2) + 6`, counting rounds from `0`. -/
def compilerElectAt (J R : ℕ) : Bool :=
  decide ((R + 8) % 42 = 0 ∧ 1 ≤ (R + 8) / 42 ∧ (R + 8) / 42 ≤ J)

/-- The fixed ordering on proposal headers (`paper.md`: "Fixed ordering": one is chosen and declared): the higher support rank first, then the
bit `false` first. -/
def betterHeader (q q' : Header) : Bool :=
  decide (q'.k < q.k) || (decide (q'.k = q.k) && (!q.b && q'.b))

/-- The chosen element of a list under the fixed ordering of headers. -/
def chooseHeader (l : List Header) : Option Header :=
  l.foldl (fun acc q =>
    match acc with
    | none => some q
    | some a => if betterHeader q a then some q else some a) none

/-- The headers appearing in a store's candidate signatures. -/
def headersIn (S : List EvRec) : List Header :=
  (S.filterMap fun e =>
    match e with
    | EvRec.headerSig q _ => some q
    | _ => none).dedup

/-- The maximum-rank verifying state among a player's own and those in its store at the Status deadline, with rank below `r`, "breaking ties by a fixed ordering" (`false`
first) (§5.2, p.15). The fallback `(false, −1)` always verifies. -/
def bestState (x : EvCtx) (S : List EvRec) (r : ℕ) (b₀ : Bool) (k₀ : ℤ) : Bool × ℤ :=
  let cands : List (Bool × ℤ) :=
    (b₀, k₀) :: (false, -1) :: (if hasSender S false then [(false, 0)] else []) ++
      (if hasSender S true then [(true, 0)] else []) ++
      ((rankBits x.J).filter fun e => decide (e.1 < r) && certValid x S e.1 e.2).map fun e => (e.2, (e.1 : ℤ))
  cands.foldl (fun a c =>
    if a.2 < c.2 ∨ (a.2 = c.2 ∧ a.1 = true ∧ c.1 = false) then c else a) (b₀, k₀)

variable {B : Type}

/-- The stage items of a player for a call, with signing: §5.2, p.16, numbered stages 1–7, and p.14 for initialization ("one shared dissemination
invocation carries the designated sender's signed bit in its source payload and empty payloads from all other players"). Everything is read from the
store as of the preceding deadline. "An honest player endorses at most one header for each candidate in an iteration, and issues endorsements only
during that iteration's Prepare-2 stage" (p.15). Forwarding calls have "empty ordinary stage payloads" (p.30). -/
def stageItems (cfg : CallCfg (List EvRec)) (input : Option Bool) (st : LS (List EvRec)) :
    Stage → PM (List EvRec) (List EvRec × LS (List EvRec))
  | Stage.init => do
    match input with
    | some b =>
      let ss ← Prog.signAll [encDatum cfg.enc (Datum.senderBit cfg.sender b)]
      pure ([EvRec.senderSig b (ss.headD [])], st)
    | none => pure ([], st)
  | Stage.status _ =>
    pure (supportClosure (cfg.ctx st) st.store st.bit st.rank, st)
  | Stage.prepare1 r => do
    let x := cfg.ctx st
    let (b, k) := bestState x st.store r st.bit st.rank
    let q : Header := ⟨r, cfg.self, b, k⟩
    let ss ← Prog.signAll [encDatum cfg.enc (Datum.header q)]
    pure (EvRec.headerSig q (ss.headD []) :: supportClosure x st.store b k,
      { st with ownHeader := q :: st.ownHeader })
  | Stage.prepare2 r => do
    let x := cfg.ctx st
    let chosen := (List.range cfg.n).filterMap fun c =>
      chooseHeader ((headersIn st.store).filter fun q =>
        decide (q.r = r ∧ q.cand = c) && headerValid x st.store q)
    let ss ← Prog.signAll (chosen.map fun q => encDatum cfg.enc (Datum.endorse cfg.self q))
    pure ((chosen.zip ss).map (fun e => EvRec.endorse e.1 cfg.self e.2), st)
  | Stage.proposal r => do
    let x := cfg.ctx st
    match st.ownHeader.find? (fun q => q.r = r) with
    | some q =>
      if preparedValid x st.store q then pure (preparedClosure x st.store q, st) else pure ([], st)
    | none => pure ([], st)
  | Stage.vote r => do
    let x := cfg.ctx st
    let h : ℤ := ((st.frozen.find? fun e => e.1 = r).map fun e => e.2.1).getD (-1)
    let ps := (headersIn st.store).filter fun q =>
      decide (q.r = r ∧ x.L r = some q.cand ∧ h ≤ q.k) && preparedValid x st.store q
    match chooseHeader ps with
    | some q =>
      let ss ← Prog.signAll [encDatum cfg.enc (Datum.vote cfg.self r q.b)]
      pure (EvRec.vote r q.b cfg.self (ss.headD []) q :: preparedClosure x st.store q, st)
    | none => pure ([], st)
  | Stage.commit r => do
    let x := cfg.ctx st
    let ok := [false, true].filter fun b =>
      certValid x st.store r b && (voters x st.store r (!b)).isEmpty
    match ok.head? with
    | some b =>
      let ss ← Prog.signAll [encDatum cfg.enc (Datum.commit cfg.self r b)]
      pure (EvRec.commit r b cfg.self (ss.headD []) :: certClosure x st.store r b, st)
    | none => pure ([], st)
  | Stage.forward => pure ([], st)

/-- State updates at a call's deadline. After initialization, "Each recipient initializes its state to a rank-0 certificate it receives, or to the bit 0 and
rank −1 if it receives none" with conflicts "resolved by a fixed ordering" (p.14). "At the Commit deadline, it accepts every higher-rank certificate carried by a
verifying commit, using the fixed ordering for ties" (p.16). -/
def deadlineUpdate (cfg : CallCfg (List EvRec)) (st : LS (List EvRec)) : Stage → LS (List EvRec)
  | Stage.init =>
    if hasSender st.store false then { st with bit := false, rank := 0 }
    else if hasSender st.store true then { st with bit := true, rank := 0 }
    else { st with bit := false, rank := -1 }
  | Stage.commit _ =>
    (rankBits cfg.J).foldl (fun s e =>
      if decide (s.rank < e.1) && decide (0 < (committers st.store e.1 e.2).length) &&
          certValid (cfg.ctx st) st.store e.1 e.2 then
        { s with bit := e.2, rank := e.1 }
      else s) st
  | _ => st

/-- The end of a call: extract the elementary evidence of the retained payloads, include it in the output snapshot, update the state and decide if a certificate is now held. -/
def closeCall (cfg : CallCfg (List EvRec)) (st : LS (List EvRec)) (stage : Stage) :
    PM (List EvRec) (LS (List EvRec)) := do
  let st ← absorbEv cfg st (st.pay.flatMap Payload.body)
  let st := st.snap fun r => { r with output := r.output.map fun o => { o with store := st.store } }
  let st := deadlineUpdate cfg st stage
  let st ← maybeDecide cfg st
  Prog.save st
  pure st

/-- One call of the compiler, §5.2 and §8.1. "At a call boundary it first fixes its ordinary or terminal mode using retained evidence, and only then generates that call's
new stage signatures and freezes its source payload" (p.29). An ordinary source signs its stage batch, even an empty one. A terminal source "may omit that stage payload and
instead supplies its chosen termination certificate and terminal acknowledgement". After the call, evidence is extracted from the retained payloads (p.15: "extracts these
elementary evidence records and discards the preceding dissemination invocation's transport envelopes"). The result also says whether this was a qualifying call. -/
def compilerCall (cfg₀ : CallCfg (List EvRec)) (input : Option Bool) (c : ℕ) (grace : Bool)
    (st : LS (List EvRec)) : PM (List EvRec) (LS (List EvRec) × Bool) := do
  let stage := stageOf cfg₀.J c
  let cfg := { cfg₀ with sid := c, iter := electIter cfg₀.J c }
  let st ← maybeDecide cfg st
  let terminal := (firstTerm (cfg.ctx st) st.store).isSome
  let st : LS (List EvRec) := { st with pay := [], ack := [] }
  let st : LS (List EvRec) := match stage with
    | Stage.status r => { st with frozen := (r, st.rank, st.bit) :: st.frozen }
    | _ => st
  if terminal then
    let bits := (termBits (cfg.ctx st) st.store).filter fun b =>
      !(st.store.any fun e =>
        match e with
        | EvRec.tack b' j _ => b' == b && decide (j = cfg.self)
        | _ => false)
    let ts ← Prog.signAll (bits.map fun b => encDatum cfg.enc (Datum.tack cfg.self b))
    let st := { st with store := st.store ++ (bits.zip ts).map fun e => EvRec.tack e.1 cfg.self e.2 }
    let st ← callProg cfg c true grace none st
    let st ← closeCall cfg st stage
    pure (st, true)
  else
    let (body, st) ← stageItems cfg input st stage
    let ss ← Prog.signAll [encDatum cfg.enc (Datum.payload c cfg.self body)]
    let p : Payload (List EvRec) := ⟨c, cfg.self, body, ss.headD []⟩
    let st ← callProg cfg c false grace (some p) { st with pay := [p] }
    let st ← closeCall cfg st stage
    pure (st, false)

/-- The whole program of player `i` (§§5.2, 8.1): `Q = 6J + 4` calls, then the public final deadline, "At the end of the third forwarding call every remaining player stops; an undecided
player outputs the fixed fallback bit 0" (p.30). After completing a qualifying call, a player participates in the two grace rounds of the next call and halts. -/
def compilerProg (n t K Bd J sender i : ℕ) (input : Option Bool) : PM (List EvRec) Unit := do
  let cfg : CallCfg (List EvRec) := ⟨n, t, K, Bd, 0, i, sender, J, none, true, encRecs⟩
  let init : LS (List EvRec) × Bool := ({}, false)
  let last ← (List.range (6 * J + 4)).foldlM
    (fun s c => compilerCall cfg input c s.2 s.1) init
  match last.1.decided with
  | some _ => pure ()
  | none =>
    Prog.decide false
    Prog.save { last.1 with decided := some false }

/-- The compiler of §5 with the adaptive dissemination of §7 and the terminal procedure of §8, with iteration cap `J`. The public round cap is `7Q`, by (32), p.33. -/
noncomputable def compiler (J : Params → ℕ) :
    Protocol (Envelope (List EvRec)) (ProgState (Envelope (List EvRec)) (LS (List EvRec))) :=
  Protocol.ofProg {}
    (fun P i x => compilerProg P.n P.t (paramK P) (paramB P) (J P) P.sender.val i.val x)
    (fun P => 7 * (6 * J P + 4)) missionOpCap (fun P R => compilerElectAt (J P) R)

end BeyondDS


