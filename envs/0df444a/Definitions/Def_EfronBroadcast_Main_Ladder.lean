-- Prove2me | Definitions.Def_EfronBroadcast_Main_Ladder
-- name    : EfronBroadcast_Main_Ladder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:36.59224+00:00
-- url     : https://prove2.me/theorems/5f64ea7e-5e89-4c7c-a05c-957ee5ca05bb
-- title:
--   RET specification and operational Ladder
-- statement:
--   The RET output specification (Definition 2) with target $M$ and original inputs $A_0,P_0$ says: if the receiver $q$ is correct, then $V\supseteq A_0$, $F\subseteq P_0$, $|V|\ge M$ whenever some member of $P_0$ is correct, and $P_0\subseteq F$ whenever $|V|<M$.
--
--   Ladder (Protocols 2 and 3) is defined by explicit local rules on the public schedule $k=\log_2 n$, $R=8k+8$, attempts of $2k+3$ rounds, scales $s=0,\dots,k$ with $c=2^s$, and $E=(k+1)R(2k+3)$. The receiver computes $D=M-|A|$, stops if $D\le0$, sets $d=\min\{c,D\}$, divides the current ordered $P$ into consecutive groups of size $\lfloor D/d\rfloor$, sends each member a signed request $\langle\mathrm{request},s,j,\rho,|P|,d\rangle_q$ with the opening of its position, runs Bisect on each group's virtual senders $(p,e)$ with $e<d$, blames a party any of whose virtual indices is $\bot$, sends each survivor the query $L_p$, unions the data received, and blames survivors who did not return $L_p$. A sender returns forever on a missing or invalid request, $m>n$, $d\notin[1,\min\{c,M\}]$, $cm>2n$, a conflicting request for the same attempt, or an invalid query, and otherwise forwards the request to its neighbours in $G_c$, runs Bisect, and answers the query.
--
--   The commitment is symbolic: the term $\rho$ is the committed list, so it cannot be opened to two values at one position. Correct parties use it only by verifying that the opened position is below the claimed length and names them, and it is charged the commitment length rather than the list's. Requests are signed together with an instance tag. When the tag has $\mathrm{cert}=\mathsf{some}\ b$, a data value $j$ stands for $j$'s signed accept message for $b$, charged one signature; when $\mathrm{cert}=\mathsf{none}$ it is a bare index, which is RET over $\mathcal V=[n]$. The value universe is $[2^k]$ with $n\le 2^k$; indices $\ge n$ count as $\bot$ and are dropped from data, which has no effect when $n=2^k$. The family $G_c$ of Lemma 2 is a parameter, with its property named separately as a predicate. No correctness or cost property is assumed by these definitions.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 5, PDF p. 6, Definition 2, Protocols 2–3; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_ComparisonGraph
import Definitions.Def_EfronBroadcast_Main_Network
import Definitions.Def_EfronBroadcast_Main_Bisect
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Definition 2: the output specification of RET with target `M`, original inputs `A₀, P₀`, for a
receiver `q`: `V ⊇ A₀`, `F ⊆ P₀`, delivery and resolution. -/
def RetOutput {n : ℕ} {V : Type} (a : Corruptions n) (q : Party n) (M : ℕ) (A₀ : Finset V)
    (P₀ : List (Party n)) (Vout : Finset V) (F : Finset (Party n)) : Prop :=
  IsCorrect a q →
    A₀ ⊆ Vout ∧ (∀ p ∈ F, p ∈ P₀) ∧
    ((∃ p ∈ P₀, IsCorrect a p) → M ≤ Vout.card) ∧
    (Vout.card < M → ∀ p ∈ P₀, p ∈ F)

/-- The family `G_c` of Lemma 2 for `c = 1, …, 2^k`, with degree constant `κ`. -/
def ComparisonFamily {n : ℕ} (κ k : ℕ) (G : ℕ → SimpleGraph (Party n)) : Prop :=
  ∀ c, 1 ≤ c → c ≤ 2 ^ k →
    (∀ v, comparisonDegree (G c) v ≤ κ * c * k) ∧ ComparisonProperty c (G c)

/-- Binds a Ladder invocation's signatures to its instance. `cert = some b` means that the value
`j` stands for `j`'s signed accept message for `b` (the broadcast instantiation of §3.2);
`cert = none` is RET over bare indices `V = [n]`. -/
structure LadderTag where
  cert : Option Bool
  epoch : ℕ
  deriving DecidableEq

/-- The signed request `⟨request, s, j, ρ, m, d⟩_q`. The commitment `ρ` is symbolic: it is the
committed list, so that a commitment cannot be opened to two values at one position. Correct
parties never read `ρ` except by verifying an opening, and it is charged `PrimitiveSizes.com`. -/
structure Request (n : ℕ) where
  signer : Party n
  tag : LadderTag
  s : ℕ
  j : ℕ
  ρ : List (Party n)
  m : ℕ
  d : ℕ
  deriving DecidableEq

/-- What can be signed. -/
inductive SignedBody (n : ℕ) where
  | accept (b : Bool)
  | request (μ : Request n)
  deriving DecidableEq

/-- Ladder's messages. `request μ pos` carries the opening of position `pos` of `μ.ρ`; `bisect e m`
is the Bisect message `m` of virtual sender `(·, e)`. -/
inductive LadderMsg (n k : ℕ) where
  | request (μ : Request n) (pos : ℕ)
  | compare (μ : Request n)
  | bisect (e : ℕ) (m : BisectMessage)
  | query (L : Finset (Fin (2 ^ k)))
  | data (L : Finset (Fin (2 ^ k)))
  | malformed (bytes : List Bool)

def natBits (v : ℕ) : ℕ := (encodeNat v).length

/-- Serialized length of a Ladder message: a tag, its integers, and the primitives it carries. The
instance tag is charged by the enclosing protocol, not here. -/
def ladderMsgBits {n k : ℕ} (Z : PrimitiveSizes) (tag : LadderTag) : LadderMsg n k → ℕ
  | .request μ pos => 3 + natBits μ.s + natBits μ.j + natBits μ.m + natBits μ.d + natBits pos +
      Z.sig + Z.com + Z.opening μ.m
  | .compare μ => 3 + natBits μ.s + natBits μ.j + natBits μ.m + natBits μ.d + Z.sig + Z.com
  | .bisect e m => 3 + natBits e + m.encode.length
  | .query L => 3 + natBits L.card + ∑ v ∈ L, natBits v.val
  | .data L => 3 + natBits L.card +
      ∑ v ∈ L, (natBits v.val + if tag.cert.isSome then Z.sig else 0)
  | .malformed bytes => 3 + bytes.length

/-- The parties named by real indices (`< n`) of a value set; indices `≥ n` are padding. -/
def realSigners {n k : ℕ} (L : Finset (Fin (2 ^ k))) : List (Party n) :=
  (List.finRange n).filter (fun p => decide (∃ v ∈ L, v.val = p.val))

/-- The signatures a Ladder message carries. -/
def ladderSigs {n k : ℕ} (tag : LadderTag) : LadderMsg n k → List (Party n × SignedBody n)
  | .request μ _ => [(μ.signer, .request μ)]
  | .compare μ => [(μ.signer, .request μ)]
  | .data L => match tag.cert with
    | some b => (realSigners L).map (fun p => (p, .accept b))
    | none => []
  | _ => []

/-! ### The public schedule -/

def attemptLength (k : ℕ) : ℕ := 2 * k + 3
def attemptsPerScale (k : ℕ) : ℕ := 8 * k + 8
/-- `E = (k + 1) R (2k + 3)`. It does not depend on the target. -/
def ladderE (k : ℕ) : ℕ := (k + 1) * attemptsPerScale k * attemptLength k

/-- Zero-based attempt containing the zero-based round `r`. -/
def roundAttempt (k r : ℕ) : ℕ := r / attemptLength k
/-- The source's round number `1, …, 2k + 3` within the attempt. -/
def roundOffset (k r : ℕ) : ℕ := r % attemptLength k + 1
/-- The scale index `s`, with `c = 2^s`. -/
def roundScale (k r : ℕ) : ℕ := roundAttempt k r / attemptsPerScale k
/-- The attempt index `j ∈ [R]` within the scale. -/
def roundTry (k r : ℕ) : ℕ := roundAttempt k r % attemptsPerScale k + 1

/-- Public parameters of one invocation. -/
structure LadderConfig (n k : ℕ) where
  G : ℕ → SimpleGraph (Party n)
  q : Party n
  M : ℕ
  tag : LadderTag

/-- The virtual senders `G × [d]` of a group, with zero-based `e`. -/
def virtualSenders {n : ℕ} (g : List (Party n)) (d : ℕ) : List (Party n × ℕ) :=
  g.flatMap (fun p => (List.range d).map (fun e => (p, e)))

/-! ### Protocol 2: the receiver -/

/-- Receiver state; `groups`, `d` and `bisect` belong to the current attempt. `done` records the
return of line 4 (or a party that is not the receiver of this instance). -/
structure LadderReceiver (n k : ℕ) where
  A : Finset (Fin (2 ^ k))
  P : List (Party n)
  F : Finset (Party n)
  done : Bool
  d : ℕ
  groups : List (List (Party n))
  bisect : List (BisectReceiver (Party n × ℕ))
  query : Party n → Finset (Fin (2 ^ k))

/-- Lines 4--6 and Bisect's initialization, at scale `s`. -/
def startAttempt {n k : ℕ} (M s : ℕ) (S : LadderReceiver n k) : LadderReceiver n k :=
  if M ≤ S.A.card then { S with done := true, d := 0, groups := [], bisect := [] }
  else
    let D := M - S.A.card
    let d := min (2 ^ s) D
    let groups := S.P.toChunks (D / d)
    { S with d := d, groups := groups,
             bisect := groups.map (fun g => initialReceiver S.A (virtualSenders g d)) }

/-- The receiver's messages in round `r`: line 7, the Bisect node messages, line 11. -/
noncomputable def ladderReceiverSend {n k : ℕ} (cfg : LadderConfig n k) (r : ℕ)
    (S : LadderReceiver n k) : List (Party n × LadderMsg n k) := by
  classical
  exact
    if ladderE k ≤ r ∨ S.done = true then [] else
    let o := roundOffset k r
    let μ : Request n := ⟨cfg.q, cfg.tag, roundScale k r, roundTry k r, S.P, S.P.length, S.d⟩
    if o = 1 then S.P.map (fun p => (p, .request μ (S.P.idxOf p)))
    else if o = 2 * k + 2 then S.P.map (fun p => (p, .query (S.query p)))
    else if o % 2 = 0 ∧ 4 ≤ o then
      (S.groups.zip S.bisect).flatMap (fun gB =>
        ((virtualSenders gB.1 S.d).filter (fun x => x ∉ gB.2.F)).map
          (fun x => (x.1, .bisect x.2 (.node (gB.2.node x)))))
    else []

/-- Round `2h` of Bisect in every group, at the delivery of the counts of round `2h - 1`. -/
noncomputable def moveGroups {n k : ℕ} (h : ℕ) (S : LadderReceiver n k)
    (inbox : List (Party n × LadderMsg n k)) : LadderReceiver n k := by
  classical
  let counts : Party n × ℕ → List BisectMessage := fun x =>
    inbox.filterMap (fun e => match e.2 with
      | .bisect e' m => if e.1 = x.1 ∧ e' = x.2 then some m else none
      | _ => none)
  exact { S with bisect := (S.groups.zip S.bisect).map (fun gB =>
    receiverMove h S.A (virtualSenders gB.1 S.d) gB.2 counts) }

/-- Bisect's output `j_(p,e)` in the group of `p`. An index `≥ n` (padding of the value universe,
absent when `n = 2^k`) counts as `⊥`. -/
noncomputable def groupLeaf {n k : ℕ} (S : LadderReceiver n k) (x : Party n × ℕ) :
    Option (Fin (2 ^ k)) := by
  classical
  exact (S.groups.zip S.bisect).findSome? (fun gB =>
    if x.1 ∈ gB.1 then
      (leafOutput (virtualSenders gB.1 S.d) gB.2 x : Option (Fin (2 ^ k))).filter
        (fun v => decide (v.val < n))
    else none)

/-- Lines 10--11: blame and the sets `L_p`. -/
noncomputable def finishBisect {n k : ℕ} (S : LadderReceiver n k) : LadderReceiver n k := by
  classical
  let F' := S.F ∪ S.P.toFinset.filter (fun p => ∃ e < S.d, groupLeaf S (p, e) = none)
  exact { S with
    F := F'
    P := S.P.filter (fun p => p ∉ F')
    query := fun p => (Finset.range S.d).biUnion (fun e => (groupLeaf S (p, e)).toFinset) }

/-- Lines 13--14, at the delivery of the data messages. Values `≥ n` are padding and are dropped. -/
noncomputable def collectData {n k : ℕ} (S : LadderReceiver n k)
    (inbox : List (Party n × LadderMsg n k)) : LadderReceiver n k := by
  classical
  let received : Party n → List (Finset (Fin (2 ^ k))) := fun p =>
    inbox.filterMap (fun e => match e.2 with
      | .data L => if e.1 = p then some L else none
      | _ => none)
  let F' := S.F ∪ S.P.toFinset.filter (fun p => S.query p ∉ received p)
  exact { S with
    A := S.A ∪ S.P.toFinset.biUnion (fun p =>
      (received p).toFinset.biUnion (fun L => L.filter (fun v => v.val < n)))
    F := F'
    P := S.P.filter (fun p => p ∉ F') }

/-- The receiver's local transition at the end of round `r`. -/
noncomputable def ladderReceiverRecv {n k : ℕ} (cfg : LadderConfig n k) (r : ℕ)
    (S : LadderReceiver n k) (inbox : List (Party n × LadderMsg n k)) : LadderReceiver n k := by
  classical
  exact
    if ladderE k ≤ r ∨ S.done = true then S else
    let o := roundOffset k r
    let h := (o - 1) / 2
    let S₁ := if o % 2 = 1 ∧ 1 ≤ h ∧ h ≤ k then moveGroups h S inbox else S
    let S₂ := if o = 2 * k + 1 then finishBisect S₁ else S₁
    if o = 2 * k + 3 then startAttempt cfg.M (roundScale k (r + 1)) (collectData S₂ inbox) else S₂

/-! ### Protocol 3: the sender -/

/-- Sender state; `returned` is the persistent return of Protocol 3. `heard` keeps the requests of
round 1 for the comparison check, and `pending` is the query to answer. -/
structure LadderSender (n k : ℕ) where
  W : Finset (Fin (2 ^ k))
  returned : Bool
  μ : Option (Request n)
  heard : List (Request n)
  node : ℕ → List Bool
  pending : Option (Finset (Fin (2 ^ k)))

/-- The sender's messages in round `r`: lines 20, 22 (Bisect line 6) and 24. -/
noncomputable def ladderSenderSend {n k : ℕ} (cfg : LadderConfig n k) (p : Party n) (r : ℕ)
    (S : LadderSender n k) : List (Party n × LadderMsg n k) := by
  classical
  exact
    if ladderE k ≤ r ∨ S.returned = true then [] else
    let o := roundOffset k r
    let h := (o - 1) / 2
    match S.μ with
    | none => []
    | some μ =>
      if o = 2 then
        ((List.finRange n).filter (fun v => (cfg.G (2 ^ roundScale k r)).Adj p v)).map
          (fun v => (v, .compare μ))
      else if o % 2 = 1 ∧ 1 ≤ h ∧ h ≤ k then
        (List.range μ.d).map (fun e => (cfg.q, .bisect e (honestCount S.W (S.node e))))
      else if o = 2 * k + 3 then
        match S.pending with
        | some L => [(cfg.q, .data L)]
        | none => []
      else []

/-- The requests carried by a batch of messages, from any source. -/
def carriedRequests {n k : ℕ} (inbox : List (Party n × LadderMsg n k)) : List (Request n) :=
  inbox.filterMap (fun e => match e.2 with
    | .request μ _ => some μ
    | .compare μ => some μ
    | _ => none)

/-- The sender's local transition at the end of round `r`: lines 18--19 after round 1, line 21
after round 2, Bisect line 4 after its even rounds, line 23 after round `2k + 2`. An opening is
verified as a position below the claimed length at which the committed list names this sender. -/
noncomputable def ladderSenderRecv {n k : ℕ} (cfg : LadderConfig n k) (p : Party n) (r : ℕ)
    (S : LadderSender n k) (inbox : List (Party n × LadderMsg n k)) : LadderSender n k := by
  classical
  exact
    if ladderE k ≤ r ∨ S.returned = true then S else
    let o := roundOffset k r
    let s := roundScale k r
    let j := roundTry k r
    let c := 2 ^ s
    let sameSlot : Request n → Prop := fun μ' =>
      μ'.signer = cfg.q ∧ μ'.tag = cfg.tag ∧ μ'.s = s ∧ μ'.j = j
    if o = 1 then
      let found := inbox.findSome? (fun e => match e.2 with
        | .request μ pos =>
          if e.1 = cfg.q ∧ sameSlot μ ∧ pos < μ.m ∧ μ.ρ[pos]? = some p then some μ else none
        | _ => none)
      match found with
      | none => { S with returned := true }
      | some μ =>
        if n < μ.m ∨ μ.d < 1 ∨ min c cfg.M < μ.d ∨ 2 * n < c * μ.m then
          { S with returned := true }
        else
          { S with μ := some μ, heard := carriedRequests inbox, node := fun _ => [],
                   pending := none }
    else
      let S₁ :=
        if o = 2 ∧ ∃ μ' ∈ S.heard ++ carriedRequests inbox, sameSlot μ' ∧ some μ' ≠ S.μ then
          { S with returned := true }
        else S
      if S₁.returned = true then S₁
      else if o = 2 * k + 2 then
        let d := (S₁.μ.map Request.d).getD 0
        let found := inbox.findSome? (fun e => match e.2 with
          | .query L => if e.1 = cfg.q ∧ L.card = d ∧ L ⊆ S₁.W then some L else none
          | _ => none)
        match found with
        | none => { S₁ with returned := true }
        | some L => { S₁ with pending := some L }
      else if o % 2 = 0 ∧ 4 ≤ o then
        { S₁ with node := fun e => senderNode (S₁.node e) (inbox.filterMap (fun x => match x.2 with
            | .bisect e' m => if x.1 = cfg.q ∧ e' = e then some m else none
            | _ => none)) }
      else S₁

/-! ### One party's local machine and one invocation -/

/-- A party's local state in one invocation: the receiver role and the sender role, either of
which may be inactive. -/
structure LadderLocal (n k : ℕ) where
  receiver : LadderReceiver n k
  sender : LadderSender n k

/-- Initial local state. `active` says whether this party is the receiver with inputs `A, P`;
`serves` whether it is a sender with input `W`. -/
def ladderLocalInit {n k : ℕ} (cfg : LadderConfig n k) (active : Bool) (A : Finset (Fin (2 ^ k)))
    (P : List (Party n)) (serves : Bool) (W : Finset (Fin (2 ^ k))) : LadderLocal n k where
  receiver :=
    if active = true then
      startAttempt cfg.M 0 ⟨A, P, ∅, false, 0, [], [], fun _ => ∅⟩
    else ⟨A, [], ∅, true, 0, [], [], fun _ => ∅⟩
  sender := ⟨W, !serves, none, [], fun _ => [], none⟩

noncomputable def ladderLocalSend {n k : ℕ} (cfg : LadderConfig n k) (p : Party n) (r : ℕ)
    (L : LadderLocal n k) : List (Party n × LadderMsg n k) :=
  ladderReceiverSend cfg r L.receiver ++ ladderSenderSend cfg p r L.sender

noncomputable def ladderLocalRecv {n k : ℕ} (cfg : LadderConfig n k) (p : Party n) (r : ℕ)
    (L : LadderLocal n k) (inbox : List (Party n × LadderMsg n k)) : LadderLocal n k :=
  ⟨ladderReceiverRecv cfg r L.receiver inbox, ladderSenderRecv cfg p r L.sender inbox⟩

/-- One invocation of Ladder as a RET protocol: the receiver's inputs `A, P`, and which parties are
senders, with inputs `W`. -/
structure LadderInstance (n k : ℕ) extends LadderConfig n k where
  A : Finset (Fin (2 ^ k))
  P : List (Party n)
  serves : Party n → Bool
  W : Party n → Finset (Fin (2 ^ k))

noncomputable def ladderMachine {n k : ℕ} (I : LadderInstance n k) :
    Machine n (LadderMsg n k) (LadderLocal n k) where
  init := fun p => ladderLocalInit I.toLadderConfig (decide (p = I.q)) I.A I.P (I.serves p) (I.W p)
  send := fun r p L => ladderLocalSend I.toLadderConfig p r L
  recv := fun r p L inbox => ladderLocalRecv I.toLadderConfig p r L inbox

/-- The input conditions of Definition 2 and Theorem 3: target `M ≤ n`, each correct sender holds at
least `M` values, and a correct receiver's `P` is a set whose correct members are senders. -/
def LadderInstance.Valid {n k : ℕ} (I : LadderInstance n k) (a : Corruptions n) : Prop :=
  I.M ≤ n ∧ (∀ v ∈ I.A, v.val < n) ∧
  (∀ p, IsCorrect a p → I.serves p = true → I.M ≤ (I.W p).card ∧ ∀ v ∈ I.W p, v.val < n) ∧
  (IsCorrect a I.q → I.P.Nodup ∧ ∀ p ∈ I.P, IsCorrect a p → I.serves p = true)

/-- The adversaries of an invocation: `t`-bounded, with ideal signatures. -/
def LadderInstance.Admissible {n k : ℕ} (I : LadderInstance n k)
    (adv : NetAdversary n (LadderMsg n k)) (t : ℕ) : Prop :=
  IsTBounded adv.corruptions t ∧ Unforgeable (ladderMachine I) adv (ladderSigs I.tag)

/-- The receiver's state at the start of (zero-based) round `r`. -/
noncomputable def ladderRecvState {n k : ℕ} (I : LadderInstance n k)
    (adv : NetAdversary n (LadderMsg n k)) (r : ℕ) : LadderReceiver n k :=
  (globalState (ladderMachine I) adv r I.q).receiver

/-- Bits sent in the receiver role over the whole schedule. -/
noncomputable def ladderReceiverBits {n k : ℕ} (Z : PrimitiveSizes) (I : LadderInstance n k)
    (adv : NetAdversary n (LadderMsg n k)) : ℕ :=
  ∑ r ∈ Finset.range (ladderE k),
    listBits (ladderMsgBits Z I.tag) (ladderReceiverSend I.toLadderConfig r (ladderRecvState I adv r))

/-- Bits sent in the sender role by all correct parties over the whole schedule. -/
noncomputable def ladderSenderBits {n k : ℕ} (Z : PrimitiveSizes) (I : LadderInstance n k)
    (adv : NetAdversary n (LadderMsg n k)) : ℕ := by
  classical
  exact ∑ p ∈ Finset.univ.filter (fun p => IsCorrect adv.corruptions p),
    ∑ r ∈ Finset.range (ladderE k), listBits (ladderMsgBits Z I.tag)
      (ladderSenderSend I.toLadderConfig p r (globalState (ladderMachine I) adv r p).sender)

end EfronBroadcast.Main


