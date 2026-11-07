-- Prove2me | Definitions.Def_ByzSigT_kSigT
-- name    : ByzSigT_kSigT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:56:21.97219+00:00
-- url     : https://prove2.me/theorems/042bf818-0a66-440f-877e-b3fc636e3e35
-- title:
--   The k-SigT protocol (Algorithms 1 and 2)
-- statement:
--   This is the protocol of the paper, run by each party $p$. Algorithm 1 runs $\mathrm{Layer}(i,u_p,J_p)$ for $i=1,\dots,k+1$, feeding each layer's output value and justification into the next, and decides $a$ and terminates upon receiving $f+1$ messages $\langle\mathrm{decided},a\rangle$.
--
--   Algorithm 2 proceeds in views with round-robin leaders. On entering a view a party sends its lock to the leader and starts a timer of duration $C=20\Delta$. A leader with an unused token waits $2\Delta$ and proposes the highest lock among at least $n-f$ suggest messages. A party casts vote1 for the first valid proposal whose lock is at least as recent as its own; a $V_a$ certificate makes it lock, cast vote2 and move on; a $V2_a$ certificate makes it cast vote3; a $V3_a$ certificate makes the leader use its token on a value-SigT. A party that holds conflicting certificates announces equiv, and one that holds a $\mathrm{SigT}^{(i)}$ certificate with no conflict announces allgood. After announcing and collecting $n-f$ allgood/equiv messages from parties outside its blame, the party outputs a value with a justification of type clean, adopt or tally, multicasting decided on a clean output in layer $k$. Layer $k+1$ runs only the view stage, and a valid $V2_a$ certificate there makes the party multicast decided and return. Parties forward all received messages.
--
--   The milestones of the mission are statements about executions of this protocol.
--
--   **Formalization Note** The handler logs the event and then applies the rules of the algorithm repeatedly until none applies. "Received" means occurring in a held term, including the party's own messages. Where the algorithm allows a choice, a fixed choice function decides, so the protocol is deterministic. The state records every output with its blame and with the layers whose tokens have been used.
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58a…), Algorithm 1, p.14 (PDF 15); Algorithm 2, pp.16–18 (PDF 17–19); §4.2, pp.14–16 (PDF 15–17)

import Mathlib
import Definitions.Def_ByzSigT_Protocol
import Definitions.Def_ByzSigT_Valid

open Classical

namespace ByzSigT

/-!
# The k-SigT protocol (Algorithms 1 and 2)

Efron, Kelkar, Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027
submission (manuscript sha256 f020c58a…), §4.2, pp.14–18 (PDF 15–19): Algorithm 1 (the k-SigT
protocol), Algorithm 2 (`Layer(i, u_p, J_p)`, lines 1–69), "Message forwarding" (p.15: "correct
parties forward all received messages (which they didn't forward beforehand)"), and the output
"Party p outputs from layer i a tuple (type, a, J)" (p.16).

`kSigT n f k Δ` is the protocol run by party `p`. Algorithm 1: `J_p ← ⊥`; for `i = 1, …, k + 1`,
`(·, u_p, J_p) ← Layer(i, u_p, J_p)`; "upon received f + 1 ⟨decided, a⟩: Decide a and terminate".

**Formalization Note (transcription choices).**
* "Received" is read as: occurring (possibly nested) in a term the party received or sent itself
  (`Holds`); a party knows its own multicasts at once. "Received a certificate" means that all
  messages of a valid certificate are held (`HasCert`); certificates are assembled as tuples.
* The handler records the event (received terms are logged and forwarded once; fired timers are
  logged; a token reply completes the pending SigT use) and then applies the `upon` rules of
  Algorithms 1–2 repeatedly, in the order 5, 7, 10, 14, 20, 25, 27, 29, 31, 36, 41, 46, until none
  applies (`runRules`); every rule that fires changes the state. If the iteration had no
  fixpoint the event would be ignored; with `n − f ≥ 1` every rule fires finitely often per event.
* A SigT use (lines 33, 38, 43) emits `useSigT (ℓ − 1) content` and blocks the layer rules until the
  environment's reply, which the model delivers at the same time; the multicast of lines 34, 40, 45
  is then sent with the returned token as `ownSigT`. `ownSigT` counts as used from the request on.
* Timers: entering view `v` starts `T_v` as a timer of duration `C = 20Δ` (line 29 fires when it
  expires: multicast viewchange for `v`, once); a leader's "Wait 2∆" (line 7) is a timer of
  duration `2Δ`, after which lines 7–8 run once for that view.
* Line 10 takes the first valid propose of the current view from `leader(v)` in arrival order among
  the received (top-level) terms and own messages, and runs at most once per view; lines 14, 27
  concern the current view; lines 20, 25, 31 monitor every view. "Have not sent a vote2 message in
  view v" (line 16) and per-view bookkeeping make every multicast happen once.
* Where Algorithm 2 lets the party choose (which certificate, which `n − f` messages, a lock "with
  the highest view", the messages of lines 52 and 63) the handler takes a fixed choice function
  (`pick`), so the protocol is deterministic.
* Line 46's justification is `justTerm i a* type own blame ms extra`, where the blame component is
  the tuple of the party's input justification and every term it holds, which contains the proofs
  against every party in its blame; `blame` is `D` of that tuple (line 2 adds every party proved
  corrupt by received evidence). `extra` is `⟨allgood, equiv⟩` for adopt (one of them the party's
  own) and for tally: `⟨0, σ⟩` with the allgood certificate of line 56, `⟨1⟩` for line 59, `⟨2, vs⟩`
  for line 61, `⟨3, vs₀, τ₀, vs₁, τ₁⟩` for lines 63–65.
* "Decide a and terminate": the party emits `decide a` and afterwards ignores every event. Messages
  are forwarded on receipt, before the decision rule runs. After returning from layer `k + 1`
  (line 26) the party only forwards and runs line 5.
* An output `(type, a, J)` of layer `i` is recorded in `outputs` with the blame tuple and the set of
  layers whose token the party has used at that moment.
-/

variable {n k : ℕ}

/-- A recorded output `(type, a, J)` of a layer. -/
structure OutRec (n k : ℕ) where
  /-- The layer `i` the output is from. -/
  layer : ℕ
  /-- Its type. -/
  type : JType
  /-- Its value `a`. -/
  value : Bool
  /-- Its justification `J` (an input justification for layer `i + 1`). -/
  just : Term n k
  /-- The blame tuple at the output (`blame = D` of it). -/
  blame : Term n k
  /-- The layers whose SigT the party has used at the output. -/
  used : Finset ℕ

/-- The status of the current layer's `ownSigT`. -/
inductive SigTUse : Type where
  | unused
  | value (a : Bool)
  | equiv

/-- The multicast waiting for a token reply. -/
inductive Pending (n k : ℕ) : Type where
  | valueSigT : Pending n k
  | equiv (σa σb : Term n k) : Pending n k
  | allgood (a : Bool) (σ : Term n k) : Pending n k

/-- The local state of a party running the k-SigT protocol. -/
structure KState (n k : ℕ) where
  terminated : Bool
  /-- Received terms and own messages, in order. -/
  log : List (Term n k)
  forwarded : List (Term n k)
  /-- Fired timer ids. -/
  fired : List ℕ
  /-- The current layer: `0` before the start, then `1, …, k + 1`. -/
  layer : ℕ
  /-- Returned from layer `k + 1` (line 26). -/
  returned : Bool
  /-- The input `u_p` of the current layer. -/
  u : Bool
  /-- The input justification `J_p` of the current layer. -/
  J : Term n k
  lockVal : Bool
  lockEv : Term n k
  /-- The lock view plus one (`0` is view `−1`). -/
  lockCode : ℕ
  view : ℕ
  castV3 : Option Bool
  sigt : SigTUse
  ownTok : Option (Term n k)
  awaiting : Option (Pending n k)
  /-- Layers whose token has been used. -/
  used : Finset ℕ
  vote1Done : Finset ℕ
  vote2Sent : Finset (ℕ × Bool)
  vote3Sent : Finset ℕ
  vcSent : Finset ℕ
  proposed : Finset ℕ
  agEqSent : Bool
  ownAgEq : Option (Term n k)
  outputs : List (OutRec n k)

/-- The initial state on input `u`. -/
def KState.init (u : Bool) : KState n k where
  terminated := false
  log := []
  forwarded := []
  fired := []
  layer := 0
  returned := false
  u := u
  J := botJust
  lockVal := u
  lockEv := botJust
  lockCode := 0
  view := 0
  castV3 := none
  sigt := .unused
  ownTok := none
  awaiting := none
  used := ∅
  vote1Done := ∅
  vote2Sent := ∅
  vote3Sent := ∅
  vcSent := ∅
  proposed := ∅
  agEqSent := false
  ownAgEq := none
  outputs := []

/-- A fixed choice: some `x` with `P x`, if any. -/
noncomputable def pick {α : Type} (P : α → Prop) : Option α :=
  if h : ∃ x, P x then some (Classical.choose h) else none

/-- `m` occurs in a term the party holds. -/
def Holds (st : KState n k) (m : Term n k) : Prop := ∃ t ∈ st.log, Term.Subterm m t

/-- All messages of the tuple `σ` are held. -/
def Assembled (st : KState n k) (σ : Term n k) : Prop :=
  ∃ ms : List (Term n k), σ = .list ms ∧ ∀ m ∈ ms, Holds st m

/-- The party holds a valid certificate `σ` of kind `κ` for `a` of layer `ℓ`. -/
def HasCert (f : ℕ) (st : KState n k) (κ : CertKind) (ℓ : ℕ) (a : Bool) (σ : Term n k) : Prop :=
  ValidCert f κ ℓ a σ ∧ Assembled st σ

/-- The party holds conflicting certificates `σa, σb` of layer `ℓ`. -/
def HasConflict (f : ℕ) (st : KState n k) (ℓ : ℕ) (σa σb : Term n k) : Prop :=
  Conflicting f ℓ σa σb ∧ Assembled st σa ∧ Assembled st σb

/-- The blame tuple: the input justification and every held term. -/
def blameTerm (st : KState n k) : Term n k := .list (st.J :: st.log)

/-- `blame`: the parties proved corrupt by `J_p` and by the received evidence (lines 2–3). -/
noncomputable def blame (f : ℕ) (st : KState n k) : Finset (Fin n) := corruptSet f (blameTerm st)

/-- The current lock as a term. -/
def lockOf (st : KState n k) : Term n k := lockTerm st.lockVal st.lockCode st.lockEv

/-- The lock code of a lock term (`0` for a malformed one). -/
def lockCodeOf : Term n k → ℕ
  | .list [_, .nat c, _] => c
  | _ => 0

/-- The value of a lock term. -/
def lockValOf : Term n k → Bool
  | .list [.nat c, _, _] => c == 1
  | _ => false

/-- `leader(v)`. -/
def leaderOf (p : Fin n) (v : ℕ) : Fin n := ⟨v % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) p.isLt)⟩

/-- Timer ids: `T_v` of layer `ℓ` and the leader's 2Δ wait in view `v` of layer `ℓ`. -/
def viewTimerId (ℓ v : ℕ) : ℕ := Nat.pair (Nat.pair ℓ v) 0
/-- See `viewTimerId`. -/
def waitTimerId (ℓ v : ℕ) : ℕ := Nat.pair (Nat.pair ℓ v) 1

/-- The token index of layer `ℓ`, if `1 ≤ ℓ ≤ k`. -/
def tokIdx (k ℓ : ℕ) : Option (Fin k) := if h : ℓ - 1 < k ∧ 1 ≤ ℓ then some ⟨ℓ - 1, h.1⟩ else none

/-- Multicast `t`: send it to every party and log it as own. -/
def mcast (st : KState n k) (t : Term n k) : KState n k × List (Action n k) :=
  ({ st with log := st.log ++ [t] }, (List.finRange n).map fun q => .send q t)

/-- Sequential composition of two state transformers, collecting actions. -/
def seqR (r₁ r₂ : KState n k → KState n k × List (Action n k)) (st : KState n k) :
    KState n k × List (Action n k) :=
  let x := r₁ st
  let y := r₂ x.1
  (y.1, x.2 ++ y.2)

/-- Do nothing. -/
def noop (st : KState n k) : KState n k × List (Action n k) := (st, [])

/-- The layer rules may run: started, not terminated, not returned, not waiting for a token. -/
def Active (st : KState n k) : Prop :=
  st.terminated = false ∧ 1 ≤ st.layer ∧ st.returned = false ∧ st.awaiting = none

/-- Lines 4–9, "upon entering view v": start `T_v`, send the suggest to `leader(v)`, and a leader
with `ownSigT = ⊥` starts its 2∆ wait. -/
noncomputable def enterView (Δ : ℝ) (p : Fin n) (st : KState n k) (v : ℕ) :
    KState n k × List (Action n k) :=
  let sug := (Msg.suggest st.layer (lockOf st) v st.J).signed p
  let wait : List (Action n k) :=
    if IsLeader p v ∧ (match st.sigt with | .unused => True | _ => False)
    then [.setTimer (waitTimerId st.layer v) (2 * Δ)] else []
  ({ st with view := v, log := st.log ++ [sug] },
    [.setTimer (viewTimerId st.layer v) (20 * Δ), .send (leaderOf p v) sug] ++ wait)

/-- Enter layer `ℓ` with input `a` and input justification `J` (fresh local variables of
Algorithm 2; line 1: enter view 0). -/
noncomputable def enterLayer (Δ : ℝ) (p : Fin n) (st : KState n k) (ℓ : ℕ) (a : Bool)
    (J : Term n k) : KState n k × List (Action n k) :=
  let st1 : KState n k :=
    { st with
      layer := ℓ
      u := a
      J := J
      lockVal := a
      lockEv := J
      lockCode := 0
      view := 0
      castV3 := none
      sigt := .unused
      ownTok := none
      awaiting := none
      vote1Done := ∅
      vote2Sent := ∅
      vote3Sent := ∅
      vcSent := ∅
      proposed := ∅
      agEqSent := false
      ownAgEq := none }
  enterView Δ p st1 0

/-- The signers of held decided messages for `a`. -/
noncomputable def decidedSigners (st : KState n k) (a : Bool) : Finset (Fin n) :=
  Finset.univ.filter fun q => Holds st ((Msg.decided a).signed q)

/-- Algorithm 1, lines 5–6: upon received `f + 1` ⟨decided, a⟩, decide `a` and terminate. -/
noncomputable def rule5 (f : ℕ) (st : KState n k) : KState n k × List (Action n k) :=
  if st.terminated = false ∧ ∃ a, f + 1 ≤ (decidedSigners st a).card then
    let a : Bool := if f + 1 ≤ (decidedSigners st false).card then false else true
    ({ st with terminated := true }, [.decide a])
  else (st, [])

/-- The held valid suggest messages of view `v` of the current layer, by sender. -/
def HeldSuggest (f : ℕ) (st : KState n k) (v : ℕ) (q : Fin n) (L J : Term n k) : Prop :=
  Holds st ((Msg.suggest st.layer L v J).signed q) ∧ ValidMsg f ((Msg.suggest st.layer L v J).signed q)

/-- Lines 7–8, after the 2∆ wait of view `v`: if at least `n − f` suggest messages for `v` were
received, multicast a propose with a lock `L` of the highest view among them, for `val(L)`. -/
noncomputable def rule7 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  if h : Active st ∧ ∃ v, waitTimerId st.layer v ∈ st.fired ∧ v ∉ st.proposed then
    let v := Nat.find h.2
    let st1 := { st with proposed := insert v st.proposed }
    let S : Finset (Fin n) := Finset.univ.filter fun q => ∃ L J, HeldSuggest f st v q L J
    if n - f ≤ S.card then
      match pick (fun x : Fin n × Term n k × Term n k => HeldSuggest f st v x.1 x.2.1 x.2.2 ∧
          ∀ q L J, HeldSuggest f st v q L J → lockCodeOf L ≤ lockCodeOf x.2.1) with
      | some x => mcast st1 ((Msg.propose st.layer (lockValOf x.2.1) x.2.1 v st.J).signed p)
      | none => (st1, [])
    else (st1, [])
  else (st, [])

/-- A valid propose of view `v` of the current layer from `leader(v)`. -/
def IsLeaderPropose (f : ℕ) (st : KState n k) (v : ℕ) (P : Term n k) : Prop :=
  (∃ (q : Fin n) (a : Bool) (L J : Term n k), IsLeader q v ∧
    P = (Msg.propose st.layer a L v J).signed q) ∧ ValidMsg f P

/-- Lines 10–13: upon the first valid propose `P` from `leader(v)` for `a` with lock `L` of view
`v'`, multicast vote1 if `v' ≥ View(lock)`. -/
noncomputable def rule10 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  if Active st ∧ st.view ∉ st.vote1Done then
    match st.log.find? (fun t => Decidable.decide (IsLeaderPropose f st st.view t)) with
    | some P =>
      let st1 := { st with vote1Done := insert st.view st.vote1Done }
      match pick (fun x : Bool × Term n k => ∃ (q : Fin n) (J : Term n k),
          P = (Msg.propose st.layer x.1 x.2 st.view J).signed q) with
      | some x =>
        if st.lockCode ≤ lockCodeOf x.2 then
          mcast st1 ((Msg.vote1 st.layer x.1 st.view P st.J).signed p)
        else (st1, [])
      | none => (st1, [])
    | none => (st, [])
  else (st, [])

/-- Lines 14–19: upon a valid `V_a` certificate of the current view `v`: lock it if `v` is later
than the lock, multicast vote2 unless one was sent in `v`, and enter view `v + 1`. -/
noncomputable def rule14 (f : ℕ) (Δ : ℝ) (p : Fin n) (st : KState n k) :
    KState n k × List (Action n k) :=
  match pick (fun x : Bool × Term n k => Active st ∧ HasCert f st (.V st.view) st.layer x.1 x.2) with
  | some x =>
    let v := st.view
    let st1 := if st.lockCode < v + 1
      then { st with lockVal := x.1, lockEv := x.2, lockCode := v + 1 } else st
    let r : KState n k × List (Action n k) :=
      if ∀ b, (v, b) ∉ st.vote2Sent then
        mcast { st1 with vote2Sent := insert (v, x.1) st1.vote2Sent }
          ((Msg.vote2 st.layer x.2 x.1 v st.J).signed p)
      else (st1, [])
    let e := enterView Δ p r.1 (v + 1)
    (e.1, r.2 ++ e.2)
  | none => (st, [])

/-- Lines 20–24 (layers `≤ k`): upon `n − f` valid vote2 messages for `a` in view `v` (a valid
`V2_a`), having sent vote2 for `a` in `v`: if `castVoteThree ∈ {⊥, a}` and `ownSigT` is unused or
for `a`, set `castVoteThree ← a` and multicast vote3. -/
noncomputable def rule20 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  match pick (fun x : ℕ × Bool × Term n k => Active st ∧ st.layer ≤ k ∧
      HasCert f st (.V2 x.1) st.layer x.2.1 x.2.2 ∧ (x.1, x.2.1) ∈ st.vote2Sent ∧
      x.1 ∉ st.vote3Sent ∧ (st.castV3 = none ∨ st.castV3 = some x.2.1) ∧
      (match st.sigt with | .unused => True | .value b => b = x.2.1 | .equiv => False)) with
  | some x =>
    mcast { st with castV3 := some x.2.1, vote3Sent := insert x.1 st.vote3Sent }
      ((Msg.vote3 st.layer x.2.2 x.2.1 x.1 st.J).signed p)
  | none => (st, [])

/-- Lines 25–26: in layer `k + 1`, upon a valid `V2_a` certificate of any view, multicast
⟨decided, a⟩ and return. -/
noncomputable def rule25 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  match pick (fun x : ℕ × Bool × Term n k => Active st ∧ st.layer = k + 1 ∧
      HasCert f st (.V2 x.1) (k + 1) x.2.1 x.2.2) with
  | some x => mcast { st with returned := true } ((Msg.decided x.2.1).signed p)
  | none => (st, [])

/-- Senders of held valid viewchange messages for view `v` of the current layer. -/
noncomputable def vcSigners (f : ℕ) (st : KState n k) (v : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun q => ∃ J : Term n k, Holds st ((Msg.viewchange st.layer v J).signed q) ∧
    ValidMsg f ((Msg.viewchange st.layer v J).signed q)

/-- Lines 27–28: upon `n − f` valid viewchange messages for the current view, enter the next. -/
noncomputable def rule27 (f : ℕ) (Δ : ℝ) (p : Fin n) (st : KState n k) :
    KState n k × List (Action n k) :=
  if Active st ∧ n - f ≤ (vcSigners f st st.view).card then enterView Δ p st (st.view + 1)
  else (st, [])

/-- Lines 29–30: upon `T_v = C`, multicast viewchange for `v` (once). -/
noncomputable def rule29 (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  if h : Active st ∧ ∃ v, viewTimerId st.layer v ∈ st.fired ∧ v ∉ st.vcSent then
    let v := Nat.find h.2
    mcast { st with vcSent := insert v st.vcSent } ((Msg.viewchange st.layer v st.J).signed p)
  else (st, [])

/-- Request the current layer's token on `content`, waiting for the reply with `pd`. -/
def request (st : KState n k) (content : Term n k) (s : SigTUse) (pd : Pending n k) :
    KState n k × List (Action n k) :=
  match tokIdx k st.layer with
  | some i => ({ st with sigt := s, awaiting := some pd, used := insert st.layer st.used },
      [.useSigT i content])
  | none => (st, [])

/-- Lines 31–35 (layers `≤ k`): upon `n − f` valid vote3 messages for `a` in view `v` with
`p = leader(v)`: if `ownSigT = ⊥` and `castVoteThree ∈ {⊥, a}`, form `V3_a` and use the token on
`(value, a, V3_a, J_p)`; the reply is then multicast. -/
noncomputable def rule31 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  match pick (fun x : ℕ × Bool × Term n k => Active st ∧ st.layer ≤ k ∧
      HasCert f st (.V3 x.1) st.layer x.2.1 x.2.2 ∧ IsLeader p x.1 ∧
      (match st.sigt with | .unused => True | _ => False) ∧
      (st.castV3 = none ∨ st.castV3 = some x.2.1)) with
  | some x => request st (valueBody x.2.1 x.2.2 st.J) (.value x.2.1) .valueSigT
  | none => (st, [])

/-- The equiv message with token `s`. -/
def equivMsg (p : Fin n) (st : KState n k) (s σa σb : Term n k) : Term n k :=
  (Msg.equiv st.layer s σa σb st.J).signed p

/-- The allgood message with token `s`. -/
def allgoodMsg (p : Fin n) (st : KState n k) (a : Bool) (s σ : Term n k) : Term n k :=
  (Msg.allgood st.layer a s σ st.J).signed p

/-- Send an allgood/equiv message `m` and record it as the party's own. -/
def sendAgEq (st : KState n k) (m : Term n k) : KState n k × List (Action n k) :=
  mcast { st with agEqSent := true, ownAgEq := some m } m

/-- Lines 36–40 (layers `≤ k`): upon conflicting certificates, having sent no allgood/equiv: use
the token on `(equiv, σa, σb, J_p)` if unused, and multicast ⟨equiv, i, ownSigT, σa, σb, J_p⟩. -/
noncomputable def rule36 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  match pick (fun x : Term n k × Term n k => Active st ∧ st.layer ≤ k ∧ st.agEqSent = false ∧
      HasConflict f st st.layer x.1 x.2) with
  | some x =>
    match st.sigt with
    | .unused => request st (equivBody x.1 x.2 st.J) .equiv (.equiv x.1 x.2)
    | _ => sendAgEq st (equivMsg p st (st.ownTok.getD (.nat 0)) x.1 x.2)
  | none => (st, [])

/-- Lines 41–45 (layers `≤ k`): upon a SigT^{(i)} certificate `σ` for `a`, no conflicting
certificates, `castVoteThree ∈ {⊥, a}`, `ownSigT` unused or for `a`, and no allgood/equiv sent: use
the token on `(value, a, σ, J_p)` if unused, and multicast ⟨allgood, i, a, ownSigT, σ, J_p⟩. -/
noncomputable def rule41 (f : ℕ) (p : Fin n) (st : KState n k) : KState n k × List (Action n k) :=
  match pick (fun x : Bool × Term n k => Active st ∧ st.layer ≤ k ∧ st.agEqSent = false ∧
      HasCert f st .sigT st.layer x.1 x.2 ∧ (¬ ∃ σa σb, HasConflict f st st.layer σa σb) ∧
      (st.castV3 = none ∨ st.castV3 = some x.1) ∧
      (match st.sigt with | .unused => True | .value b => b = x.1 | .equiv => False)) with
  | some x =>
    match st.sigt with
    | .unused => request st (valueBody x.1 x.2 st.J) (.value x.1) (.allgood x.1 x.2)
    | _ => sendAgEq st (allgoodMsg p st x.1 (st.ownTok.getD (.nat 0)) x.2)
  | none => (st, [])

/-- A held valid allgood/equiv message of layer `ℓ` from `q`. -/
def HeldAgEq (f : ℕ) (st : KState n k) (ℓ : ℕ) (q : Fin n) (s : Term n k) : Prop :=
  Holds st s ∧ ValidMsg f s ∧ ((∃ a, IsAllgoodOf q ℓ a s) ∨ IsEquivOf q ℓ s)

/-- `n − f` held valid allgood/equiv messages of the current layer from distinct parties outside
blame (line 46). -/
def OutputSet (f : ℕ) (st : KState n k) (ms : List (Term n k)) : Prop :=
  ms.length = n - f ∧ (ms.filterMap Term.signer).Nodup ∧
    ∀ s ∈ ms, ∃ q, s.signer = some q ∧ q ∉ blame f st ∧ HeldAgEq f st st.layer q s

/-- The value of an allgood message. -/
def agValue : Term n k → Bool
  | .sig _ (.list [_, _, .nat c, _, _, _]) => c == 1
  | _ => false

/-- Lines 47–68: the output `(type, a*, J)` of the current layer from the `n − f` messages `ms`. -/
noncomputable def outputOf (f : ℕ) (p : Fin n) (st : KState n k) (ms : List (Term n k)) :
    JType × Bool × Term n k × Bool :=
  -- the result: type, a*, extra evidence, whether to multicast ⟨decided, a*⟩ (line 50)
  let ℓ := st.layer
  let own := st.ownAgEq.getD (.nat 0)
  if ¬ ∃ q s, Holds st s ∧ ValidMsg f s ∧ IsEquivOf q ℓ s then
    -- lines 48–50: clean
    let a := match ms with | s :: _ => agValue s | [] => false
    (.clean, a, .list [], Decidable.decide (ℓ = k))
  else if ∃ q a s, Holds st s ∧ ValidMsg f s ∧ IsAllgoodOf q ℓ a s then
    -- line 52: adopt, with an allgood message for a and an equiv message, one of them own
    if ∃ a, IsAllgoodOf p ℓ a own then
      match pick (fun eq : Term n k => Holds st eq ∧ ValidMsg f eq ∧ ∃ q, IsEquivOf q ℓ eq) with
      | some eq => (.adopt, agValue own, .list [own, eq], false)
      | none => (.adopt, agValue own, .list [own], false)
    else
      match pick (fun ag : Term n k => Holds st ag ∧ ValidMsg f ag ∧ ∃ q a, IsAllgoodOf q ℓ a ag) with
      | some ag => (.adopt, agValue ag, .list [ag, own], false)
      | none => (.adopt, false, .list [own], false)
  else
    -- lines 54–67: tally
    let Vs : Set Bool := {c | ∃ q s, Holds st s ∧ ValidMsg f s ∧ IsValueSigTOf q ℓ c s}
    match pick (fun x : Bool × Term n k => ℓ = k ∧ 2 ≤ k ∧
        HasCert f st .allgood (k - 1) x.1 x.2) with
    | some x => (.tally, x.1, .list [.nat 0, x.2], false)            -- lines 56–57
    | none =>
      if Vs = ∅ then (.tally, st.u, .list [.nat 1], false)            -- lines 58–59
      else if Vs = {true} ∨ Vs = {false} then                          -- lines 60–61
        let c : Bool := Decidable.decide (Vs = {true})
        match pick (fun vs : Term n k => Holds st vs ∧ ValidMsg f vs ∧ ∃ q, IsValueSigTOf q ℓ c vs) with
        | some vs => (.tally, c, .list [.nat 2, vs], false)
        | none => (.tally, c, .list [.nat 2], false)
      else                                                             -- lines 62–65
        let ch := fun (c : Bool) => pick (fun x : Term n k × Term n k => Holds st x.1 ∧
          ChoiceV (Valid f) ℓ c x.1 x.2)
        match ch false, ch true with
        | some x₀, some x₁ =>
          (.tally, tallyWinner (certSigners x₀.2) (certSigners x₁.2) (certSigners (.list ms)),
            .list [.nat 3, x₀.1, x₀.2, x₁.1, x₁.2], false)
        | _, _ => (.tally, false, .list [.nat 3], false)

/-- Lines 46–69 (layers `≤ k`): having sent an allgood/equiv message, upon valid allgood/equiv
messages from `n − f` parties outside blame: output `(type, a*, J)` and enter the next layer with
`u_p ← a*`, `J_p ← J` (Algorithm 1, line 3). -/
noncomputable def rule46 (f : ℕ) (Δ : ℝ) (p : Fin n) (st : KState n k) :
    KState n k × List (Action n k) :=
  match pick (fun ms : List (Term n k) => Active st ∧ st.layer ≤ k ∧ st.agEqSent = true ∧
      OutputSet f st ms) with
  | some ms =>
    let o := outputOf f p st ms
    let own := st.ownAgEq.getD (.nat 0)
    let Jnew := justTerm st.layer o.2.1 o.1 own (blameTerm st) ms o.2.2.1
    let rec_ : OutRec n k := ⟨st.layer, o.1, o.2.1, Jnew, blameTerm st, st.used⟩
    let st1 := { st with outputs := st.outputs ++ [rec_] }
    let d : KState n k × List (Action n k) :=
      if o.2.2.2 = true then mcast st1 ((Msg.decided o.2.1).signed p) else (st1, [])
    let e := enterLayer Δ p d.1 (st.layer + 1) o.2.1 Jnew
    (e.1, d.2 ++ e.2)
  | none => (st, [])

/-- One pass of the `upon` rules, in order. -/
noncomputable def pass (f : ℕ) (Δ : ℝ) (p : Fin n) : KState n k → KState n k × List (Action n k) :=
  seqR (rule5 f) <| seqR (rule7 f p) <| seqR (rule10 f p) <| seqR (rule14 f Δ p) <|
  seqR (rule20 f p) <| seqR (rule25 f p) <| seqR (rule27 f Δ p) <| seqR (rule29 p) <|
  seqR (rule31 f p) <| seqR (rule36 f p) <| seqR (rule41 f p) <| rule46 f Δ p

/-- `m` passes, collecting actions. -/
noncomputable def passIter (f : ℕ) (Δ : ℝ) (p : Fin n) : ℕ → KState n k →
    KState n k × List (Action n k)
  | 0, st => (st, [])
  | m + 1, st =>
    let x := pass f Δ p st
    let y := passIter f Δ p m x.1
    (y.1, x.2 ++ y.2)

/-- Apply the rules until none fires (the first `m` with an unchanged pass). -/
noncomputable def runRules (f : ℕ) (Δ : ℝ) (p : Fin n) (st : KState n k) :
    KState n k × List (Action n k) :=
  if h : ∃ m, (pass f Δ p (passIter f Δ p m st).1).1 = (passIter f Δ p m st).1
  then passIter f Δ p (Nat.find h) st else (st, [])

/-- Complete a pending SigT use with the returned token `t` (lines 34, 40, 45). -/
def complete (p : Fin n) (st : KState n k) (pd : Pending n k) (t : Term n k) :
    KState n k × List (Action n k) :=
  let st1 := { st with ownTok := some t, awaiting := none }
  match pd with
  | .valueSigT => mcast st1 t
  | .equiv σa σb => sendAgEq st1 (equivMsg p st1 t σa σb)
  | .allgood a σ => sendAgEq st1 (allgoodMsg p st1 a t σ)

/-- The handler of the k-SigT protocol. -/
noncomputable def kStep (f : ℕ) (Δ : ℝ) (p : Fin n) (st : KState n k) (e : LocalEvent n k) :
    KState n k × List (Action n k) :=
  if st.terminated = true then (st, []) else
  let pre : KState n k × List (Action n k) :=
    match e with
    | .start => if st.layer = 0 then enterLayer Δ p st 1 st.u botJust else (st, [])
    | .recv _ t =>
      if t ∈ st.forwarded then ({ st with log := st.log ++ [t] }, [])
      else ({ st with log := st.log ++ [t], forwarded := st.forwarded ++ [t] },
        (List.finRange n).map fun q => .send q t)
    | .timer id => ({ st with fired := st.fired ++ [id] }, [])
    | .sigtReply i t =>
      match st.awaiting, tokIdx k st.layer with
      | some pd, some i' => if i = i' then complete p st pd t else (st, [])
      | _, _ => (st, [])
  let r := runRules f Δ p pre.1
  (r.1, pre.2 ++ r.2)

/-- The k-SigT protocol for `n` parties tolerating `f` faults with delay bound `Δ`. -/
noncomputable def kSigT (n f k : ℕ) (Δ : ℝ) : Protocol n k where
  State := KState n k
  init := fun _ u => KState.init u
  step := kStep f Δ

end ByzSigT


