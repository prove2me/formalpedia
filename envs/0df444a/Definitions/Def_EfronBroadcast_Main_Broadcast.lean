-- Prove2me | Definitions.Def_EfronBroadcast_Main_Broadcast
-- name    : EfronBroadcast_Main_Broadcast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:31.888199+00:00
-- url     : https://prove2.me/theorems/8c00c381-9064-4a69-800a-bb5aeb490e4d
-- title:
--   BB specification, Protocol 1 and its Dolev–Strong branch
-- statement:
--   The BB specification (Definition 1) for a machine with decisions, up to round $R$, states termination (every correct party has decided by $R$, sends nothing and keeps its decision from $R$ on), agreement, and validity for the leader's input.
--
--   Protocol 1 is defined by explicit local rules. With $E$ from Ladder, $T=\lceil t/E\rceil$ and $M_i=\min\{iE+1,t+1\}$: round 0; then for each epoch $E$ steps of two rounds and $E$ retrieval rounds, followed by the final test, for $1+3TE$ rounds in all. In step $s$, a party with $b\notin B$, at least $s$ valid accept messages and the leader's among them accepts $b$ and multicasts its own accept with the leader's; in the second round, one that just accepted with fewer than $M_i$ valid messages multicasts its certificate. For each bit in parallel, a party with $b\notin B$ runs Ladder as receiver with target $M_i$ on its valid messages and on $P_b$, the direct accepters of this epoch outside $F$, and adds Ladder's blame to $F$ only if $|V|<M_i$; a party that accepted in this epoch with at least $M_i$ messages serves every receiver as a Ladder sender. The final test accepts every bit with $t+1$ valid signers including the leader. The output is the sole element of $B$ if $|B|=1$, and $0$ otherwise.
--
--   A non-leader's accept message counts only once the leader's is held. The input bit is read by the leader only, in round 0. If $t<E$, line 1 selects Dolev–Strong: the leader signs and multicasts in round 0; for $1\le r\le t$ a party holding $r$ signers including the leader accepts and multicasts $r+1$ signatures; after the delivery of round $t$ it accepts on $t+1$ signers including the leader and outputs, for $t+1$ rounds. Every message's serialized length is charged, with primitives at their parameter lengths.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 2, PDF p. 3, Definition 1, Protocol 1, §3.1; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Ladder
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Definition 1 for a machine with decisions, over rounds up to `R`: termination (every correct
party has decided and halted by `R`), agreement, and validity for the leader `ℓ`'s input. -/
def BBSpec {n : ℕ} {Msg State : Type} (m : Machine n Msg State) (decision : State → Option Bool)
    (ℓ : Party n) (input : Bool) (adv : NetAdversary n Msg) (R : ℕ) : Prop :=
  (∀ p, IsCorrect adv.corruptions p →
    (decision (globalState m adv R p)).isSome = true ∧
    ∀ r, R ≤ r → sentAt m adv r p = [] ∧
      decision (globalState m adv r p) = decision (globalState m adv R p)) ∧
  (∀ p p', IsCorrect adv.corruptions p → IsCorrect adv.corruptions p' →
    decision (globalState m adv R p) = decision (globalState m adv R p')) ∧
  (IsCorrect adv.corruptions ℓ → ∀ p, IsCorrect adv.corruptions p →
    decision (globalState m adv R p) = some input)

/-- Protocol 1's messages. `accept b L` and `certificate b L` carry the signed accept messages for
`b` of the signers `L`; `ladder q b i m` belongs to the epoch-`i` invocation of receiver `q` for `b`. -/
inductive BBMsg (n k : ℕ) where
  | accept (b : Bool) (L : Finset (Fin (2 ^ k)))
  | certificate (b : Bool) (L : Finset (Fin (2 ^ k)))
  | ladder (q : Party n) (b : Bool) (i : ℕ) (m : LadderMsg n k)
  | malformed (bytes : List Bool)

/-- The tag of the epoch-`i` invocation for bit `b`: signatures are bound to bit and epoch. -/
def bbTag (b : Bool) (i : ℕ) : LadderTag := ⟨some b, i⟩

def bbMsgBits {n k : ℕ} (Z : PrimitiveSizes) : BBMsg n k → ℕ
  | .accept _ L => 3 + natBits L.card + ∑ v ∈ L, (natBits v.val + Z.sig)
  | .certificate _ L => 3 + natBits L.card + ∑ v ∈ L, (natBits v.val + Z.sig)
  | .ladder q b i m => 3 + natBits q.val + 1 + natBits i + ladderMsgBits Z (bbTag b i) m
  | .malformed bytes => 3 + bytes.length

def bbSigs {n k : ℕ} : BBMsg n k → List (Party n × SignedBody n)
  | .accept b L => (realSigners L).map (fun p => (p, .accept b))
  | .certificate b L => (realSigners L).map (fun p => (p, .accept b))
  | .ladder _ b i m => ladderSigs (bbTag b i) m
  | .malformed _ => []

/-- Public parameters. Values are indices in `Fin (2^k)`; `n ≤ 2^k`, with `n = 2^k` in the source. -/
structure BBConfig (n k : ℕ) where
  hn : n ≤ 2 ^ k
  G : ℕ → SimpleGraph (Party n)
  leader : Party n
  t : ℕ

/-- `T = ⌈t / E⌉`. -/
def epochCount (k t : ℕ) : ℕ := (t + ladderE k - 1) / ladderE k
/-- `M_i = min {iE + 1, t + 1}`. -/
def epochTarget (k t i : ℕ) : ℕ := min (i * ladderE k + 1) (t + 1)

/-- Where a round lies in the fixed schedule of Protocol 1 for `t ≥ E`: round `0`; then for each
epoch `E` steps of two rounds followed by `E` retrieval rounds. -/
inductive BBPhase where
  | zero
  | acceptOne (i s : ℕ)
  | acceptTwo (i s : ℕ)
  | retrieve (i rr : ℕ)
  | over

def bbPhase (k t r : ℕ) : BBPhase :=
  if r = 0 then .zero else
  let E := ladderE k
  let i := (r - 1) / (3 * E) + 1
  let w := (r - 1) % (3 * E)
  if epochCount k t < i then .over
  else if w < 2 * E then
    if w % 2 = 0 then .acceptOne i ((i - 1) * E + 1 + w / 2)
    else .acceptTwo i ((i - 1) * E + 1 + w / 2)
  else .retrieve i (w - 2 * E)

/-- First round of the epoch `i` acceptance phase. -/
def acceptanceStart (k i : ℕ) : ℕ := 1 + (i - 1) * (3 * ladderE k)
/-- First round of the epoch `i` retrieval phase. -/
def retrievalStart (k i : ℕ) : ℕ := acceptanceStart k i + 2 * ladderE k
/-- First round after the epoch `i` retrieval phase. -/
def retrievalEnd (k i : ℕ) : ℕ := acceptanceStart k i + 3 * ladderE k

/-- The total number of rounds; line 1 selects Dolev--Strong when `t < E`. -/
def bbRounds (k t : ℕ) : ℕ :=
  if t < ladderE k then t + 1 else 1 + 3 * epochCount k t * ladderE k

/-- Local state of Protocol 1. `raw b` is every signer whose accept message for `b` is held. -/
structure BBState (n k : ℕ) where
  raw : Bool → Finset (Fin (2 ^ k))
  B : Finset Bool
  F : Finset (Party n)
  sentEpoch : Bool → Option ℕ
  sentStep : Bool → Option ℕ
  direct : Bool → Finset (Party n)
  P : Bool → List (Party n)
  serving : Bool → Bool
  ladder : Bool → Party n → LadderLocal n k
  decision : Option Bool

section Protocol

variable {n k : ℕ} (cfg : BBConfig n k)

/-- A party's index in the value universe. -/
def embedParty (p : Party n) : Fin (2 ^ k) := Fin.castLE cfg.hn p

/-- `A_p(b)`: a non-leader's accept message is valid only once the leader's has been received. -/
noncomputable def validAccepts (s : BBState n k) (b : Bool) : Finset (Fin (2 ^ k)) := by
  classical
  exact if embedParty cfg cfg.leader ∈ s.raw b then s.raw b else ∅

/-- Line 6's test at step `st`. -/
noncomputable def canAccept (s : BBState n k) (b : Bool) (st : ℕ) : Prop :=
  b ∉ s.B ∧ st ≤ (validAccepts cfg s b).card ∧ embedParty cfg cfg.leader ∈ s.raw b

/-- Line 17's test. -/
noncomputable def finalTest (s : BBState n k) (b : Bool) : Prop :=
  cfg.t + 1 ≤ (validAccepts cfg s b).card ∧ embedParty cfg cfg.leader ∈ s.raw b

/-- Line 18. Output the sole element of `B` if `|B| = 1`, and `0` otherwise; `0` is `false`, so
the output is `true` exactly when `B = {true}`. -/
def decideBit (B : Finset Bool) : Bool := decide (B = {true})

def multicast (m : BBMsg n k) : List (Party n × BBMsg n k) :=
  (List.finRange n).map (fun d => (d, m))

/-- The invocation configuration of bit `b`, receiver `q` in epoch `i`. -/
def bbLadderConfig (b : Bool) (q : Party n) (i : ℕ) : LadderConfig n k :=
  ⟨cfg.G, q, epochTarget k cfg.t i, bbTag b i⟩

/-- Absorb the accept messages carried by the delivered messages; indices `≥ n` are padding. -/
noncomputable def absorb (inbox : List (Party n × BBMsg n k)) (s : BBState n k) :
    BBState n k := by
  classical
  exact { s with raw := fun b => s.raw b ∪ (inbox.flatMap (fun e => match e.2 with
    | .accept b' L => if b' = b then (L.filter (fun v => v.val < n)).toList else []
    | .certificate b' L => if b' = b then (L.filter (fun v => v.val < n)).toList else []
    | _ => [])).toFinset }

/-- Direct accepts: `⟨accept, b⟩_{p'}` received from `p'` itself. -/
noncomputable def noteDirect (inbox : List (Party n × BBMsg n k)) (s : BBState n k) :
    BBState n k := by
  classical
  exact { s with direct := fun b => s.direct b ∪ (inbox.filterMap (fun e => match e.2 with
    | .accept b' L => if b' = b ∧ embedParty cfg e.1 ∈ L then some e.1 else none
    | _ => none)).toFinset }

/-- Local effect of round 1 of step `st` (lines 6--7): accept and hold one's own signature. -/
noncomputable def applyAccept (p : Party n) (i st : ℕ) (s : BBState n k) : BBState n k := by
  classical
  let acc : Bool → Prop := fun b => canAccept cfg s b st
  exact { s with
    B := s.B ∪ Finset.univ.filter acc
    raw := fun b => if acc b then insert (embedParty cfg p) (s.raw b) else s.raw b
    sentEpoch := fun b => if acc b then some i else s.sentEpoch b
    sentStep := fun b => if acc b then some st else s.sentStep b }

/-- Lines 10--16: the start of the retrieval phase. `P_b` keeps a direct accepter only if its accept
message is valid, that is, once the leader's accept message for `b` is held. -/
noncomputable def startRetrieval (p : Party n) (i : ℕ) (s : BBState n k) : BBState n k := by
  classical
  let Pb : Bool → List (Party n) := fun b =>
    if embedParty cfg cfg.leader ∈ s.raw b then
      (List.finRange n).filter (fun x => x ∈ s.direct b ∧ x ∉ s.F)
    else []
  let serve : Bool → Bool := fun b =>
    decide (b ∈ s.B ∧ s.sentEpoch b = some i ∧
      epochTarget k cfg.t i ≤ (validAccepts cfg s b).card)
  exact { s with
    P := Pb
    serving := serve
    ladder := fun b q => ladderLocalInit (bbLadderConfig cfg b q i)
      (decide (q = p ∧ b ∉ s.B)) (validAccepts cfg s b) (Pb b) (serve b) (validAccepts cfg s b) }

/-- The messages of the invocation `(q, b, i)` in a batch. -/
def routeLadder (q : Party n) (b : Bool) (i : ℕ) (inbox : List (Party n × BBMsg n k)) :
    List (Party n × LadderMsg n k) :=
  inbox.filterMap (fun e => match e.2 with
    | .ladder q' b' i' m => if q' = q ∧ b' = b ∧ i' = i then some (e.1, m) else none
    | _ => none)

/-- Line 14, for both bits. -/
noncomputable def endRetrieval (p : Party n) (i : ℕ) (s : BBState n k) : BBState n k := by
  classical
  let V : Bool → Finset (Fin (2 ^ k)) := fun b => (s.ladder b p).receiver.A
  let short : Bool → Prop := fun b =>
    b ∉ s.B ∧ (V b).card < epochTarget k cfg.t i
  exact { s with
    raw := fun b => if b ∉ s.B then s.raw b ∪ V b else s.raw b
    F := s.F ∪ Finset.univ.biUnion (fun b => if short b then (s.ladder b p).receiver.F else ∅)
    direct := fun _ => ∅
    sentStep := fun _ => none }

/-- Lines 17--18. -/
noncomputable def finalDecision (s : BBState n k) : BBState n k := by
  classical
  let B' := s.B ∪ Finset.univ.filter (fun b => finalTest cfg s b)
  exact { s with B := B', decision := some (decideBit B') }

/-- Round 0's local effect at the leader (line 3). -/
def leaderStart (p : Party n) (input : Bool) (s : BBState n k) : BBState n k := by
  classical
  exact if p = cfg.leader then
    { s with B := {input}, raw := fun b => if b = input then {embedParty cfg p} else s.raw b }
  else s

/-- Protocol 1's sends for `t ≥ E`. Only the leader's sends in round 0 read `input`. -/
noncomputable def mainSend (input : Bool) (r : ℕ) (p : Party n) (s : BBState n k) :
    List (Party n × BBMsg n k) := by
  classical
  exact match bbPhase k cfg.t r with
  | .zero => if p = cfg.leader then multicast (.accept input {embedParty cfg p}) else []
  | .acceptOne _ st =>
      ([false, true].filter (fun b => canAccept cfg s b st)).flatMap (fun b =>
        multicast (.accept b {embedParty cfg p, embedParty cfg cfg.leader}))
  | .acceptTwo i st =>
      ([false, true].filter (fun b => s.sentStep b = some st ∧
          (validAccepts cfg s b).card < epochTarget k cfg.t i)).flatMap (fun b =>
        multicast (.certificate b (validAccepts cfg s b)))
  | .retrieve i rr =>
      [false, true].flatMap (fun b => (List.finRange n).flatMap (fun q =>
        (ladderLocalSend (bbLadderConfig cfg b q i) p rr (s.ladder b q)).map
          (fun e => (e.1, BBMsg.ladder q b i e.2))))
  | .over => []

/-- Protocol 1's local transitions for `t ≥ E`. -/
noncomputable def mainRecv (input : Bool) (r : ℕ) (p : Party n) (s : BBState n k)
    (inbox : List (Party n × BBMsg n k)) : BBState n k :=
  let E := ladderE k
  match bbPhase k cfg.t r with
  | .zero => absorb inbox (leaderStart cfg p input s)
  | .acceptOne i st => noteDirect cfg inbox (absorb inbox (applyAccept cfg p i st s))
  | .acceptTwo i st =>
      let s₁ := noteDirect cfg inbox (absorb inbox s)
      if st = i * E then startRetrieval cfg p i s₁ else s₁
  | .retrieve i rr =>
      let next : Bool → Party n → LadderLocal n k := fun b q =>
        ladderLocalRecv (bbLadderConfig cfg b q i) p rr (s.ladder b q) (routeLadder q b i inbox)
      let s₁ := absorb inbox { s with ladder := next }
      if rr + 1 = E then
        let s₂ := endRetrieval cfg p i s₁
        if i = epochCount k cfg.t then finalDecision cfg s₂ else s₂
      else s₁
  | .over => s

/-- The certificate of Dolev--Strong's round `r`: one's own signature, the leader's, and `r - 1`
others, for `r + 1` signatures. -/
noncomputable def dsCertificate (p : Party n) (r : ℕ) (s : BBState n k) (b : Bool) :
    Finset (Fin (2 ^ k)) := by
  classical
  exact {embedParty cfg p, embedParty cfg cfg.leader} ∪
    (((((validAccepts cfg s b).erase (embedParty cfg cfg.leader)).erase
      (embedParty cfg p)).toList.mergeSort (fun x y => x.val ≤ y.val)).take (r - 1)).toFinset

/-- Dolev--Strong's sends (§3.1): the leader in round 0; for `1 ≤ r ≤ t`, a party accepting `b`
because it holds signatures of `r` signers including the leader multicasts `r + 1` signatures. -/
noncomputable def dsSend (input : Bool) (r : ℕ) (p : Party n) (s : BBState n k) :
    List (Party n × BBMsg n k) := by
  classical
  exact
    if r = 0 then
      if p = cfg.leader then multicast (.accept input {embedParty cfg p}) else []
    else if r ≤ cfg.t then
      ([false, true].filter (fun b => canAccept cfg s b r)).flatMap (fun b =>
        multicast (.accept b (dsCertificate cfg p r s b)))
    else []

/-- Dolev--Strong's local transitions; after the delivery of round `t` a party accepts on `t + 1`
signatures including the leader's and outputs (acceptance in the source's last round `t + 1`). -/
noncomputable def dsRecv (input : Bool) (r : ℕ) (p : Party n) (s : BBState n k)
    (inbox : List (Party n × BBMsg n k)) : BBState n k :=
  if cfg.t < r then s else
  let s₁ := if r = 0 then leaderStart cfg p input s else applyAccept cfg p 0 r s
  let s₂ := absorb inbox s₁
  if r = cfg.t then finalDecision cfg s₂ else s₂

/-- Protocol 1, including line 1: the local rules of every party. `input` is read only by the
leader, in round 0. -/
noncomputable def bbMachine (input : Bool) : Machine n (BBMsg n k) (BBState n k) where
  init := fun _ => ⟨fun _ => ∅, ∅, ∅, fun _ => none, fun _ => none, fun _ => ∅, fun _ => [],
    fun _ => false,
    fun b q => ladderLocalInit (bbLadderConfig cfg b q 0) false ∅ [] false ∅, none⟩
  send := fun r p s => if cfg.t < ladderE k then dsSend cfg input r p s else mainSend cfg input r p s
  recv := fun r p s inbox =>
    if cfg.t < ladderE k then dsRecv cfg input r p s inbox else mainRecv cfg input r p s inbox

/-- The adversaries against Protocol 1: `t`-bounded, with ideal signatures. -/
def BBAdmissible (input : Bool) (adv : NetAdversary n (BBMsg n k)) : Prop :=
  IsTBounded adv.corruptions cfg.t ∧ Unforgeable (bbMachine cfg input) adv bbSigs

/-- Local state of a party at the start of (zero-based) round `r`. -/
noncomputable def bbState (input : Bool) (adv : NetAdversary n (BBMsg n k)) (r : ℕ) (p : Party n) :
    BBState n k :=
  globalState (bbMachine cfg input) adv r p

end Protocol

end EfronBroadcast.Main


