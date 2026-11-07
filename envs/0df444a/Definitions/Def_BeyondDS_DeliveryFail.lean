-- Prove2me | Definitions.Def_BeyondDS_DeliveryFail
-- name    : BeyondDS_DeliveryFail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:12:53.82444+00:00
-- url     : https://prove2.me/theorems/3fb73fbc-d1a2-4f50-b165-ac36c8acc25d
-- title:
--   Delivery obligations, the stopping boundary $g$ and the constants of §8
-- statement:
--   Events and quantities on outcomes of the compiler and of stand-alone dissemination:
--
--   1. **Epoch failures** of Lemma 7.4 for the two epochs of a call: no set of at most $B$ exceptional sources outside which every source uncorrupted through the epoch has its frozen data delivered to every recipient uncorrupted through the epoch.
--   2. **Required delivery** (§7.1): every source uncorrupted through round 5 has its initial payload in the output of every recipient uncorrupted through round 7; for a terminal source (§8.1) the obligation is "receipt of some verifying termination certificate for its bit". A **possession invariant** holds when $t+1$ witnesses that processed round 5 hold the payload (or a termination certificate for the bit). A statistical delivery failure is a required-delivery failure whose possession invariant holds.
--   3. **Unforged record sets**: every signature verifies under the honest keys and each signature of a forever-honest identity is on data that identity signed, the model of a certificate that "exists, even if assembled privately".
--   4. **The stopping boundary $g$** (§8.3): the first call-completion boundary at which some player that began that call with a termination certificate is still uncorrupted, or $\infty$; $N$, the main iterations begun before $g$, capped at $J$; relevant failures before $g$ and in the call after $g$ (§8.4).
--   5. **Constants**: $\delta=2\delta_{ep}+n\delta_{fin}$ (sparse) or $0$ (dense); $q=1/2+\zeta+6\delta$ of (28); $D=(6J+4)(6nH+n^2)$, $H=\min\{K,n\}$, of (30); $c_A=6nK+2nB+2n^2\delta_{ep}$, $c_T=8nK+nB+n^2\delta_{ep}$ of (27), and $n(n-1)$, $2n(n-1)$ in the dense case.
--   6. The law of the configuration after $R$ rounds, successful stopping prefixes at $g$, forgeries before a boundary, and the events $\epsilon_{sig}$ ("an accepted acknowledgement attributed to a currently uncorrupted identity has signed data (Ack, sid, P) that this identity never signed") and "some required payload is not delivered" of Theorem 7.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §7.1, p.22 (PDF p.23); Lemma 7.4, p.24; §8, pp.29–33 (PDF pp.30–34), eqs. (27), (28), (30)

import Mathlib
import Definitions.Def_BeyondDS_compiler
import Definitions.Def_BeyondDS_Fail
import Definitions.Def_BeyondDS_TrialStep

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal Classical

namespace BeyondDS

/-- The message type of the compiler. -/
abbrev CMsg := Envelope (List EvRec)
/-- The local state type of the compiler. -/
abbrev CSt := ProgState CMsg (LS (List EvRec))

section Generic

variable {B : Type} {n : ℕ} {σ : Type}

/-- The readable part of the last state of `i`. -/
def viewOf (ω : Config n (Envelope B) (ProgState (Envelope B) (LS B)) σ) (i : Fin n) : LS B :=
  (ω.st i).view

/-- The record of call `c` of player `i`. -/
def recOf (ω : Config n (Envelope B) (ProgState (Envelope B) (LS B)) σ) (i : Fin n) (c : ℕ) :
    Option (CallRec B) :=
  (viewOf ω i).calls.find? fun r => r.call = c

/-- Failure of the conclusion of Lemma 7.4 (p.24) for the first epoch of call `c`, beginning at round `R₀`: no set of at most `B` exceptional sources
outside which every source uncorrupted through the epoch has its whole frozen data delivered to every recipient uncorrupted through the epoch. -/
def Epoch1Fail [DecidableEq B] (Bd R₀ c : ℕ) (ω : Config n (Envelope B) (ProgState (Envelope B) (LS B)) σ) : Prop :=
  ¬ ∃ X : Finset (Fin n), X.card ≤ Bd ∧ ∀ s, s ∉ X → ω.UncorruptedThrough s (R₀ + 1) →
    ∀ r, ω.UncorruptedThrough r (R₀ + 1) → ∀ rs rr o, recOf ω s c = some rs → recOf ω r c = some rr →
      rr.after2 = some o →
      (∀ p ∈ rs.frozen1.pay, p ∈ o.pay) ∧ (∀ e ∈ rs.frozen1.term, e ∈ o.store)

/-- Failure of the conclusion of Lemma 7.4 for the second epoch of call `c` (rounds 3–4), which carries the frozen acknowledgement buffers and the terminal
acknowledgements. -/
def Epoch2Fail [DecidableEq B] (Bd R₀ c : ℕ) (ω : Config n (Envelope B) (ProgState (Envelope B) (LS B)) σ) : Prop :=
  ¬ ∃ X : Finset (Fin n), X.card ≤ Bd ∧ ∀ s, s ∉ X → ω.UncorruptedThrough s (R₀ + 3) →
    ∀ r, ω.UncorruptedThrough r (R₀ + 3) → ∀ rs rr f o, recOf ω s c = some rs → recOf ω r c = some rr →
      rs.frozen3 = some f → rr.after4 = some o →
      (∀ a ∈ f.ack, a ∈ o.ack) ∧ (∀ e ∈ tacks f.store, e ∈ o.store)

/-- Required delivery of §7.1, p.22 fails in the instance with call index `c` starting at round `R₀`: "every source uncorrupted through the end of round 5 to have its initial
payload included in the output of every recipient uncorrupted through the end of round 7". A recipient that has no output, because it halted or was corrupted before processing the
last boundary, has no obligation. -/
def OrdinaryDeliveryFail (R₀ c : ℕ) (ω : Config n (Envelope B) (ProgState (Envelope B) (LS B)) σ) (s r : Fin n)
    (p : Payload B) : Prop :=
  ω.UncorruptedThrough s (R₀ + 4) ∧ ω.UncorruptedThrough r (R₀ + 6) ∧
    (recOf ω s c).bind CallRec.source = some p ∧
    ∃ rr o, recOf ω r c = some rr ∧ rr.output = some o ∧ p ∉ o.pay

/-- A set of `t + 1` witnesses for payload `p` at the recovery boundary of call `c`: each witness that went on to process the boundary of round 5 holds `p`
(§7.3, p.24; §7.6, p.28: "there is a witness set of size at least t + 1 with the possession property"). -/
def Possession (t c : ℕ) (ω : Config n (Envelope B) (ProgState (Envelope B) (LS B)) σ) (p : Payload B) : Prop :=
  ∃ A : Finset (Fin n), t + 1 ≤ A.card ∧ ∀ j ∈ A, ∀ rj b, recOf ω j c = some rj → rj.after5 = some b → p ∈ b.pay

end Generic

section Compiler

variable {n : ℕ} {σ : Type}

/-- The public evidence context of an outcome: election outputs from the transcript. The `r` of the election at the boundary of round `R` is `(R + 8) / 42`, by `compilerElectAt`. -/
def publicCtx (P : Params) (J : ℕ) (ω : Config P.n CMsg CSt σ) : EvCtx :=
  ⟨P.n, P.t, P.sender.val, J,
    ω.log.filterMap fun e =>
      match e with
      | Event.obs (Obs.elected R l) => some ((R + 8) / 42, l.val)
      | _ => none⟩

/-- A candidate certificate object, in the flat form of records, held by anybody: "even if it is assembled privately" (Lemma 5.2, p.17). All its signatures verify under the honest keys, and
"no signatures are forged": each signature attributed to a forever-honest identity is on data that identity signed. -/
def Unforged (S : Sig) (P : Params) (J : ℕ) (ω : Config P.n CMsg CSt σ) (W : List EvRec) : Prop :=
  ∀ e ∈ W, (e.inDomain (publicCtx P J ω) = true) ∧
    let q := e.query encRecs (publicCtx P J ω)
    ω.checks S q.1 q.2.1 q.2.2 = true ∧
      ∀ j : Fin P.n, j.val = q.1 → ω.ForeverHonest j → (j, q.2.1) ∈ ω.signLog

/-- A verifying certificate for `b` at rank `r` in a record set. -/
def Unforged.IsCert (P : Params) (J : ℕ) (ω : Config P.n CMsg CSt σ) (W : List EvRec) (r : ℕ) (b : Bool) : Prop :=
  certValid (publicCtx P J ω) W r b = true

/-- A forever-honest player issued a commit for `b` in iteration `r`. -/
def IssuedCommit (P : Params) (ω : Config P.n CMsg CSt σ) (r : ℕ) (b : Bool) : Prop :=
  ∃ i : Fin P.n, ω.ForeverHonest i ∧ (i, encDatum encRecs (Datum.commit i.val r b)) ∈ ω.signLog

/-- The bit of a terminal source: its decision. -/
def termBitOf (ω : Config n CMsg CSt σ) (s : Fin n) : Option Bool :=
  (viewOf ω s).decided

/-- A snapshot holds a verifying termination certificate for `b`. -/
def Buf.HoldsTerm (x : EvCtx) (o : Buf (List EvRec)) (b : Bool) : Prop :=
  ∃ r, termValid x o.store r b = true

/-- The delivery obligation of a terminal source fails in call `c`: "a terminal source's delivery obligation is receipt of some verifying termination certificate for its bit" (§8.1, p.30). -/
def TerminalDeliveryFail (P : Params) (J c : ℕ) (ω : Config P.n CMsg CSt σ) (s r : Fin P.n) (b : Bool) : Prop :=
  ω.UncorruptedThrough s (7 * c + 4) ∧ ω.UncorruptedThrough r (7 * c + 6) ∧
    (∃ rs, recOf ω s c = some rs ∧ rs.terminal = true) ∧ termBitOf ω s = some b ∧
    ∃ rr o, recOf ω r c = some rr ∧ rr.output = some o ∧ ¬ o.HoldsTerm (publicCtx P J ω) b

/-- The acknowledgement-possession invariant of a terminal source at recovery: "A terminal source uncorrupted through round 5 creates t + 1 witnesses whose currently uncorrupted members hold some
verifying termination certificate for its bit" (p.31). -/
def TerminalPossession (P : Params) (J c : ℕ) (ω : Config P.n CMsg CSt σ) (b : Bool) : Prop :=
  ∃ A : Finset (Fin P.n), P.t + 1 ≤ A.card ∧ ∀ j ∈ A, ∀ rj o, recOf ω j c = some rj → rj.after5 = some o →
    o.HoldsTerm (publicCtx P J ω) b

/-- A statistical delivery failure in call `c` (§8.4, p.32): a required ordinary-payload or terminal-predicate delivery fails while its possession invariant holds at its recovery boundary. -/
def DeliveryFail (P : Params) (J c : ℕ) (ω : Config P.n CMsg CSt σ) : Prop :=
  (∃ s r p, OrdinaryDeliveryFail (7 * c) c ω s r p ∧ Possession P.t c ω p) ∨
    ∃ s r b, TerminalDeliveryFail P J c ω s r b ∧ TerminalPossession P J c ω b

/-- A terminal-source failure of Lemma 8.1 (p.31): "the probability that a terminal source's required delivery fails while its acknowledgement-possession invariant holds at recovery". -/
def TerminalFail (P : Params) (J c : ℕ) (ω : Config P.n CMsg CSt σ) : Prop :=
  ∃ s r b, TerminalDeliveryFail P J c ω s r b ∧ TerminalPossession P J c ω b

/-- The event that every required delivery of §5.1, p.14 has occurred: "the required dissemination invocations succeed". Both obligations of §8.1, in every call, unconditionally. -/
def Delivered (P : Params) (J : ℕ) (ω : Config P.n CMsg CSt σ) : Prop :=
  ∀ c, (∀ s r p, ¬ OrdinaryDeliveryFail (7 * c) c ω s r p) ∧ ∀ s r b, ¬ TerminalDeliveryFail P J c ω s r b

/-- `Qualifies ω c`: call `c` has completed and some player that began it with a termination certificate is still uncorrupted (§8.3, p.31). -/
def Qualifies (ω : Config n CMsg CSt σ) (c : ℕ) : Prop :=
  7 * c + 7 ≤ ω.round ∧ ∃ i, ω.UncorruptedThrough i (7 * c + 6) ∧ ∃ r, recOf ω i c = some r ∧ r.terminal = true

/-- The stopping boundary `g` of §8.3, p.31, as a call index: "the first call-completion boundary at which some player that began that call with a termination certificate is still uncorrupted. If no
such completion occurs, set g = ∞" (`none`). -/
noncomputable def gCall (ω : Config n CMsg CSt σ) : Option ℕ :=
  if h : ∃ c, Qualifies ω c then some (Nat.find h) else none

/-- `N` of §8.4, p.32: "main iterations begun before g, capped at J". Iteration `r` begins with call `6(r − 1) + 1`. -/
noncomputable def itersBegun (J : ℕ) (ω : Config n CMsg CSt σ) : ℕ :=
  ((Finset.Icc 1 J).filter fun r =>
    match gCall ω with
    | some g => 6 * (r - 1) + 1 ≤ g
    | none => True).card

/-- Calls before or at `g`, and the call after `g`, are the ones whose statistics count (§8.4, p.32): "In the call after g, only failure of its first epoch matters". The first clause collects the failures of a call reached before `g`, in the sparse
case; in the dense case only delivery counts. -/
def RelevantFailure (P : Params) (J : ℕ) (ω : Config P.n CMsg CSt σ) : Prop :=
  Forge ω ∨
  (∃ c, (∀ g, gCall ω = some g → c ≤ g) ∧
    (DeliveryFail P J c ω ∨
      (paramK P < P.n ∧ (Epoch1Fail (paramB P) (7 * c) c ω ∨ Epoch2Fail (paramB P) (7 * c) c ω)))) ∨
  (∃ g, gCall ω = some g ∧ paramK P < P.n ∧ Epoch1Fail (paramB P) (7 * (g + 1)) (g + 1) ω)

end Compiler

/-- `δ` of p.32: "For the sparse case define δ = 2δep + nδfin, using (14) and (15); in the dense case put δ = 0." -/
noncomputable def bigDelta (P : Params) : ℝ :=
  if paramK P < P.n then 2 * deltaEp P.n (paramK P) + P.n * deltaFin P.n (paramK P) else 0

/-- `q` of (28), p.32. -/
noncomputable def qVal (P : Params) (ζ : ℝ) : ℝ := 1 / 2 + ζ + 6 * bigDelta P

/-- `D` of (30), p.32, with `H = min{K, n}`. -/
noncomputable def bigD (P : Params) (J : ℕ) : ℕ :=
  (6 * J + 4) * (6 * P.n * min (paramK P) P.n + P.n ^ 2)

/-- The values of `cA` and `cT` of (27), p.31, and in the dense case `n(n − 1)` and `2n(n − 1)`. -/
noncomputable def cA (P : Params) : ℝ :=
  if paramK P < P.n then
    6 * P.n * paramK P + 2 * P.n * paramB P + 2 * (P.n : ℝ) ^ 2 * deltaEp P.n (paramK P)
  else P.n * (P.n - 1)

/-- See `cA`. -/
noncomputable def cT (P : Params) : ℝ :=
  if paramK P < P.n then
    8 * P.n * paramK P + P.n * paramB P + (P.n : ℝ) ^ 2 * deltaEp P.n (paramK P)
  else 2 * P.n * (P.n - 1)

/-- The law of the configuration after `R` rounds of the execution, with the setup: "a fixed reachable prefix" is a point of its support. -/
noncomputable def prefixLaw {Msg St : Type} (Pi : Protocol Msg St) (S : Sig) (P : Params) (x : Bool)
    (E : List (Event P.n Msg St) → PMF (Fin P.n)) (A : Adversary P.n Msg St) (R : ℕ) :
    PMF (Config P.n Msg St A.σ) :=
  (setup Pi S P x A).bind (runRounds Pi S P E A R)

section Stopping

variable {σ : Type}

/-- Evidence a player has received by a boundary, whether or not it has processed it yet: the bodies of the payloads it holds or has just been delivered in round 7 of call `c`, and the evidence delivered with them,
keeping only records with valid signatures in payloads with valid signatures. -/
noncomputable def boundaryEvidence (S : Sig) (P : Params) (J c : ℕ) (cf : Config P.n CMsg CSt σ) (i : Fin P.n) : List EvRec :=
  let x := publicCtx P J cf
  let incoming : List CMsg :=
    match cf.resp i with
    | Resp.boundary inbox _ => (inbox.map Prod.snd).filter fun e => decide (e.sid = c ∧ e.round = 7)
    | _ => []
  let pays := (viewOf cf i).pay ++ (incoming.flatMap Envelope.pay).filter fun p =>
    cf.checks S p.src (encDatum encRecs (Datum.payload p.sid p.src p.body)) p.sig
  let raw := pays.flatMap Payload.body ++ incoming.flatMap Envelope.term
  (viewOf cf i).store ++ raw.filter fun e =>
    e.inDomain x && (let q := e.query encRecs x; cf.checks S q.1 q.2.1 q.2.2)

/-- A successful stopping prefix at the boundary of call `g` (Lemma 8.1, p.31: "on histories with no such delivery or authentication failure
through g, every player uncorrupted at g has a termination certificate at that boundary. […] The tail bound in (27) is conditional on any such
successful stopping prefix at g"): no forgery has occurred, no statistical delivery failure has occurred in a call before `g` (the outputs of
call `g` itself are processed only after this prefix), and every player uncorrupted at `g` holds a termination certificate at that boundary. -/
def SuccessfulStop (S : Sig) (P : Params) (J g : ℕ) (cf : Config P.n CMsg CSt σ) : Prop :=
  ¬ Forge cf ∧ gCall cf = some g ∧ (∀ c, c < g → ¬ DeliveryFail P J c cf) ∧
    ∀ i, i ∉ cf.corrupted → ∃ r b, termValid (publicCtx P J cf) (boundaryEvidence S P J g cf i) r b = true

/-- A forgery (the event of `Forge`) occurs before the delivery boundary of round `R` (counted from `0`): in a prefix of the transcript that
does not yet contain that boundary. If the boundary never occurs, every forgery counts. This is "authentication failure through g" of Lemma 8.1
(p.31), with `R = 7g + 7`: the outputs of call `g` are processed in the first activation after its last boundary, before the boundary of round
`7g + 7`. -/
def ForgeBefore {n : ℕ} {Msg St : Type} (R : ℕ) (ω : Config n Msg St σ) : Prop :=
  ∃ (pre : List (Event n Msg St)) (i j : Fin n) (m : Str), pre <+: ω.log ∧ Event.forgery i j m ∈ pre ∧
    Event.obs (Obs.boundary R) ∉ pre

/-- No honest transmission after the boundary of round `R`. -/
def NoSendAfter {P : Params} (R : ℕ) (ω : Config P.n CMsg CSt σ) : Prop :=
  ∀ pre post, ω.log = pre ++ Event.obs (Obs.boundary R) :: post →
    ∀ i j m, Event.obs (Obs.sent i j m) ∉ post

end Stopping

section DissemEvents

variable {n : ℕ} {σ : Type}

/-- The outcomes of stand-alone dissemination have bit-string bodies. -/
abbrev DCfg (n : ℕ) (σ : Type) := Config n (Envelope Str) (ProgState (Envelope Str) (LS Str)) σ

/-- The event `ϵsig` bounds (§7.1, p.22): "an accepted acknowledgement attributed to a currently uncorrupted identity has signed data (Ack, sid, P) that this identity never signed". -/
def AckForge (sid : ℕ) (ω : DCfg n σ) : Prop :=
  ∃ (i j : Fin n) (P : Payload Str), Event.forgery i j (encDatum id (Datum.ack sid j.val P)) ∈ ω.log ∧
    (j, encDatum id (Datum.ack sid j.val P)) ∉ ω.signLog

/-- "some required payload is not delivered", (21), p.27. -/
def NotDelivered (sid : ℕ) (ω : DCfg n σ) : Prop :=
  ∃ s r p, OrdinaryDeliveryFail 0 sid ω s r p

/-- Payload records supplied by the adversary, including those inside acknowledgements. -/
def advPayloads (ω : DCfg n σ) : List (Payload Str) :=
  ω.log.flatMap fun e =>
    match e with
    | Event.injected _ _ m => m.pay ++ m.ack.map Ack.payload
    | _ => []

/-- Acknowledgement records supplied by the adversary. -/
def advAcks (ω : DCfg n σ) : List (Ack Str) :=
  ω.log.flatMap fun e =>
    match e with
    | Event.injected _ _ m => m.ack
    | _ => []

/-- The initial source payloads of the call. -/
def initialPayloads (sid : ℕ) (ω : DCfg n σ) : List (Payload Str) :=
  (List.finRange n).filterMap fun i => (recOf ω i sid).bind CallRec.source

/-- All payload records retained by any player. -/
def retainedPay (ω : DCfg n σ) : List (Payload Str) :=
  (List.finRange n).flatMap fun i => (viewOf ω i).pay

/-- All acknowledgement records retained by any player. -/
def retainedAck (ω : DCfg n σ) : List (Ack Str) :=
  (List.finRange n).flatMap fun i => (viewOf ω i).ack

end DissemEvents

end BeyondDS


