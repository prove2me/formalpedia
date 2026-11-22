-- Prove2me | Definitions.Def_BeyondDS_Supplement_Sortition
-- name    : BeyondDS_Supplement_Sortition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:09:07.783821+00:00
-- url     : https://prove2.me/theorems/1b7d475a-e311-4efa-b076-f9346685dd21
-- title:
--   The self-sortition agreement protocol of §10.2 and its execution in the ideal-table model of §10.1
-- statement:
--   This definition gives the model of §10.1 and the protocol of §10.2, in both alternatives.
--
--   **Parameters.** There are $n$ players, at most $f$ adaptive corruptions, a committee parameter $\ell$ with certificate threshold $k=\ell/2$, a cap $V$ on the ordinary iterations and $q$ candidate registration domains.
--
--   **Eligibility.** A label is a message type (Vote, Commit, Status, Propose, Terminate), an iteration and, in the binary alternative only, the bit of the signed datum. In each candidate domain $j$, each key $i$ has an evaluation $Y_j(i,\lambda)$ at each label $\lambda$; all evaluations are independent and uniform on $\{0,\dots,n-1\}$. A key is eligible for a label when its evaluation is below the threshold of the label's type, $1$ for Propose and $\ell$ otherwise, so with probability $1/n$ and $\ell/n$. The **erasure alternative** has labels $(T,r)$, arbitrary values, and a phase key that is erased with each completed eligibility action. The **binary alternative** has labels $(T,r,b)$ and no erasure.
--
--   **Certificates.** A rank-$0$ vote certificate is a placeholder for any value. A rank-$r$ vote certificate for $b$ has signatures on $(\mathrm{Vote},r,b)$ by $k$ distinct players and, for $r\ge2$, one proposal for $(r,b)$, which contains a vote certificate for $b$ of rank below $r$. A commit certificate for $(r,b)$ has signatures on $(\mathrm{Commit},r,b)$ by $k$ distinct players and a rank-$r$ vote certificate for $b$. Iterations lie in $\{1,\dots,V+1\}$, a vote certificate of rank $r$ is accepted only from the end of its vote round $4r-3$, and a commit certificate only from the end of its commit round $4r-2$.
--
--   **Protocol.** Rounds are numbered $1,\dots,4V+3$. Iteration $1$ has a vote round and a commit round; iteration $r\ge2$ has the rounds Status, Propose, Vote, Commit, numbered $4r-5,\dots,4r-2$. In each round an active honest player processes the messages of the type and iteration of the round that just ended, retains the highest-rank vote certificate it knows, and then acts:
--
--   1. Status: it records its highest certificate as its snapshot, of rank $h$, and conditionally multicasts it.
--   2. Propose: it conditionally multicasts a proposal for the value of its highest certificate, with that certificate.
--   3. Vote: in iteration $1$ it conditionally multicasts a vote for its input. In iteration $r\ge2$ it chooses a delivered valid proposal of highest supporting rank $u$ and conditionally multicasts a vote for its value exactly when $u\ge h$.
--   4. Commit: it conditionally multicasts a commit for $b$ if it assembled a rank-$r$ vote certificate for $b$ and accepted no iteration-$r$ vote for another value.
--
--   "Conditionally" means that the player evaluates its key at the label of the message and multicasts only if it is eligible; the evaluation, the proof and the multicast form one indivisible action. A player that obtains a valid commit certificate, assembled after a commit round or carried by a termination message, performs the terminal action in the next round in place of the ordinary one: it tests its terminal eligibility once, multicasts the certificate if eligible, decides its value and halts in either case. Round $4V+3$ allows terminal actions only. At the final boundary every still-active player decides the value of a valid commit certificate if it has one and a fixed default value otherwise. Ties are broken by a fixed public order.
--
--   **Adversary.** In the registration phase the adversary corrupts players, adaptively and within its budget, sees the evaluations of each corrupted key in every candidate domain, and then selects one domain. Online, it is rushing and adaptive: it orders the honest actions of a round, sees each honest eligibility test with its evaluation and each honest multicast, corrupts players between actions (learning their evaluations and state), and sends arbitrary messages through corrupted identities. It cannot split an honest action or delay a delivery.
--
--   **Authenticity.** Signatures and eligibility proofs are ideal. A token (signer, type, iteration, value) is **authentic** if its signer is eligible for its label in the selected domain and either the signer multicast it while honest, or the signer is corrupted and, in the erasure alternative, did not complete an eligibility action for that label while honest. The **authenticity failure** is the event that an honest player accepts a message containing a token that is not authentic.
--
--   **Measures.** $T$ is the first round at whose end no uncorrupted player is active. $M$ is $n-1$ times the number of honest multicasts. Correctness is agreement and strong unanimity over the players that are never corrupted.
--
--   **Formalization Note** The source normalizes an evaluation to a uniform point of $[0,1]$; the grid $\{0,1/n,\dots,(n-1)/n\}$ gives the same eligibility probabilities. A multicast is also delivered to its sender at no cost, which is the source's rule that a player's own tokens are available locally.
-- source:
--   Rambaud, Beyond Dolev–Strong: Adaptive Byzantine Broadcast with Õ(n^{3/2}) Messages at a Tight Honest Majority, STOC 2027 submission (manuscript sha256 c84cf9c9…), §10.1, pp.37–38 (PDF pp.38–39); §10.2, pp.38–40 (PDF pp.39–41); §10.3, p.40 (PDF p.41); §4.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_BeyondDS_Fail

set_option autoImplicit false

open scoped ENNReal

namespace BeyondDS.Supplement

/-- The message types of the self-sortition agreement protocol of Rambaud, *Beyond Dolev–Strong*, STOC 2027
submission (manuscript sha256 c84cf9c9…), §10.2, pp.38–39 (PDF 39–40). -/
inductive MType where
  | vote
  | commit
  | status
  | propose
  | terminate
  deriving DecidableEq

instance : Fintype MType :=
  ⟨{MType.vote, MType.commit, MType.status, MType.propose, MType.terminate},
    fun x => by cases x <;> simp⟩

/-- An eligibility label (§10.1, p.38): a message type, an iteration in `{0, …, V + 1}` (`0` for the terminal
label) and, in the binary alternative only, the bit of the signed datum. "In the erasure alternative, an
eligibility label is a pair (T, r) […]. In the binary alternative, […] the label is (T, r, b)". -/
abbrev Label (V : ℕ) := MType × Fin (V + 2) × Option Bool

/-- The two alternatives of §10.1, p.38. `tag v` is the value-specific part of a label and `erase` says
whether the phase signing key is erased with each completed eligibility action.

* erasure alternative: `tag = fun _ => none`, `erase = true`, arbitrary values;
* binary alternative: `tag` injective with values `some b`, `erase = false`. -/
structure Alt (Val : Type) where
  tag : Val → Option Bool
  erase : Bool

/-- A token (§10.3, p.39): "the signed type, iteration, and value together with its eligibility proof", with
its signer. The terminal token has iteration `0`. -/
structure Token (n : ℕ) (Val : Type) where
  signer : Fin n
  ty : MType
  iter : ℕ
  val : Val
  deriving DecidableEq

/-- A vote certificate (§10.2, p.38). `zero b`: "A rank-zero certificate is a public placeholder permitted for
any input value." `first b voters`: a rank-1 certificate, signatures on `(Vote, 1, b)`. `next r b voters p s`:
a rank-`r` certificate for `r ≥ 2`, signatures on `(Vote, r, b)` and one proposal for `(r, b)` by `p`, which
"contains a vote certificate for b of rank strictly less than r", namely `s`. "Each vote certificate contains
only one supporting proposal". -/
inductive VC (n : ℕ) (Val : Type) where
  | zero (b : Val)
  | first (b : Val) (voters : List (Fin n))
  | next (r : ℕ) (b : Val) (voters : List (Fin n)) (proposer : Fin n) (support : VC n Val)

namespace VC

variable {n : ℕ} {Val : Type}

/-- The rank of a vote certificate. -/
def rank : VC n Val → ℕ
  | zero _ => 0
  | first _ _ => 1
  | next r _ _ _ _ => r

/-- The value of a vote certificate. -/
def val : VC n Val → Val
  | zero b => b
  | first b _ => b
  | next _ b _ _ _ => b

/-- The tokens of a vote certificate, with those of its whole supporting chain. -/
def tokens : VC n Val → List (Token n Val)
  | zero _ => []
  | first b vs => vs.map fun j => ⟨j, MType.vote, 1, b⟩
  | next r b vs p s => (vs.map fun j => ⟨j, MType.vote, r, b⟩) ++ ⟨p, MType.propose, r, b⟩ :: s.tokens

/-- The structural checks of a vote certificate at the delivery boundary of round `now` (§10.2, p.38), with
threshold `k`: `k` signatures by distinct players; "Every iteration label […] anywhere in its attached
certificate chain must belong to {1, . . . , V + 1}"; ranks "strictly decrease along these references"; and
"A vote certificate is not accepted before the end of its designated vote round", which is round `4r − 3`.
Signatures and eligibility proofs are ideal objects, see `SCfg.legit`. -/
def valid [DecidableEq Val] (k V now : ℕ) : VC n Val → Bool
  | zero _ => true
  | first _ vs => decide (k ≤ vs.dedup.length ∧ 1 ≤ now)
  | next r b vs _ s =>
    decide (2 ≤ r ∧ r ≤ V + 1 ∧ k ≤ vs.dedup.length ∧ 4 * r ≤ now + 3 ∧ s.val = b ∧ s.rank < r) &&
      valid k V now s

end VC

/-- A commit certificate for `(r, b)` (§10.2, p.38): "k eligible signatures on (Commit, r, b) by distinct
players and a valid rank-r vote certificate for b". -/
structure CC (n : ℕ) (Val : Type) where
  r : ℕ
  b : Val
  committers : List (Fin n)
  vc : VC n Val

/-- The structural checks of a commit certificate at the boundary of round `now`: "a commit certificate is not
accepted before the end of its designated commit round", which is round `4r − 2`. -/
def CC.valid {n : ℕ} {Val : Type} [DecidableEq Val] (k V now : ℕ) (c : CC n Val) : Bool :=
  decide (1 ≤ c.r ∧ c.r ≤ V + 1 ∧ k ≤ c.committers.dedup.length ∧ 4 * c.r ≤ now + 2 ∧
    c.vc.rank = c.r ∧ c.vc.val = c.b) && c.vc.valid k V now

/-- A multicast message (§10.2, pp.38–39): a signed core `(type, iteration, value)` by `j` and its attachment.
"An individual vote in iteration r ≥ 2 carries a valid proposal for its value, and an individual commit carries
the corresponding vote certificate"; a status message carries the snapshot; a proposal carries its supporting
certificate; a termination message carries a commit certificate. -/
inductive SMsg (n : ℕ) (Val : Type) where
  | vote (j : Fin n) (r : ℕ) (b : Val) (prop : Option (Fin n × VC n Val))
  | commit (j : Fin n) (r : ℕ) (b : Val) (vc : VC n Val)
  | status (j : Fin n) (r : ℕ) (Q : VC n Val)
  | propose (j : Fin n) (r : ℕ) (b : Val) (support : VC n Val)
  | terminate (j : Fin n) (b : Val) (cc : CC n Val)

namespace SMsg

variable {n : ℕ} {Val : Type}

/-- The signed core of a message. -/
def core : SMsg n Val → Token n Val
  | vote j r b _ => ⟨j, MType.vote, r, b⟩
  | commit j r b _ => ⟨j, MType.commit, r, b⟩
  | status j r Q => ⟨j, MType.status, r, Q.val⟩
  | propose j r b _ => ⟨j, MType.propose, r, b⟩
  | terminate j b _ => ⟨j, MType.terminate, 0, b⟩

/-- Every token of a message: its core and the tokens of its attachments. An attachment to a vote of iteration
`1`, which needs none, is not examined ("unrelated extra attachments are ignored", p.39). -/
def tokens : SMsg n Val → List (Token n Val)
  | vote j r b none => [⟨j, MType.vote, r, b⟩]
  | vote j r b (some (p, s)) =>
    if r = 1 then [⟨j, MType.vote, r, b⟩]
    else ⟨j, MType.vote, r, b⟩ :: ⟨p, MType.propose, r, b⟩ :: s.tokens
  | commit j r b vc => ⟨j, MType.commit, r, b⟩ :: vc.tokens
  | status j r Q => ⟨j, MType.status, r, Q.val⟩ :: Q.tokens
  | propose j r b s => ⟨j, MType.propose, r, b⟩ :: s.tokens
  | terminate j b cc =>
    ⟨j, MType.terminate, 0, b⟩ :: (cc.committers.map fun i => ⟨i, MType.commit, cc.r, cc.b⟩) ++ cc.vc.tokens

/-- The vote certificates a message carries, which its recipient may retain. -/
def certs : SMsg n Val → List (VC n Val)
  | vote _ _ _ none => []
  | vote _ r _ (some (_, s)) => if r = 1 then [] else [s]
  | commit _ _ _ vc => [vc]
  | status _ _ Q => [Q]
  | propose _ _ _ s => [s]
  | terminate _ _ cc => [cc.vc]

end SMsg

/-- The iteration of round `R ≥ 1` (§10.2, p.39): rounds `1, 2` are the vote and commit rounds of iteration `1`,
and iteration `r ≥ 2` has the four rounds `4r − 5, …, 4r − 2`. -/
def iterOf (R : ℕ) : ℕ := (R + 5) / 4

/-- The phase of round `R`: `0` status, `1` propose, `2` vote, `3` commit. -/
def phaseOf (R : ℕ) : ℕ := (R + 1) % 4

/-- Whether an active player processes a message delivered in round `now` (§10.2, p.39): "an active player
processes the messages of the type and iteration prescribed for the round that just ended. An ordinary message
received outside that phase is ignored, including its attachments. […] Termination messages are the exception:
a valid commit certificate in such a message can trigger the terminal action at any round boundary." Ordinary
rounds are `1, …, 4V + 2`. -/
def accepts {n : ℕ} {Val : Type} [DecidableEq Val] (k V now : ℕ) : SMsg n Val → Bool
  | SMsg.vote _ r b prop =>
    decide (now ≤ 4 * V + 2 ∧ phaseOf now = 2 ∧ r = iterOf now) &&
      (decide (r = 1) ||
        match prop with
        | some (_, s) => s.valid k V now && decide (s.val = b ∧ s.rank < r)
        | none => false)
  | SMsg.commit _ r b vc =>
    decide (now ≤ 4 * V + 2 ∧ phaseOf now = 3 ∧ r = iterOf now ∧ vc.rank = r ∧ vc.val = b) &&
      vc.valid k V now
  | SMsg.status _ r Q =>
    decide (now ≤ 4 * V + 2 ∧ phaseOf now = 0 ∧ r = iterOf now) && Q.valid k V now
  | SMsg.propose _ r b s =>
    decide (now ≤ 4 * V + 2 ∧ phaseOf now = 1 ∧ r = iterOf now ∧ s.val = b ∧ s.rank < r) &&
      s.valid k V now
  | SMsg.terminate _ b cc => cc.valid k V now && decide (cc.b = b)

/-- The fixed public total order of §10.2, p.39 ("Every tie below is resolved by one fixed public total order on
the finite encodings being compared"), given by keys: the smaller key wins. The statements take the keys
injective. -/
structure Ties (n : ℕ) (Val : Type) where
  vc : VC n Val → ℕ
  prop : Fin n × VC n Val → ℕ
  cc : CC n Val → ℕ

/-- The element of smallest key; among equal keys, the first. -/
def pickMin {α : Type} (key : α → ℕ) : List α → Option α
  | [] => none
  | a :: l =>
    match pickMin key l with
    | none => some a
    | some b => if key b < key a then some b else some a

/-- "Each honest player retains the highest-rank vote certificates it has received, breaking ties
deterministically" (§10.2, p.39). -/
def pickBest {n : ℕ} {Val : Type} (T : Ties n Val) (l : List (VC n Val)) : Option (VC n Val) :=
  pickMin T.vc (l.filter fun c => decide (c.rank = (l.map VC.rank).foldl max 0))

/-- The local state of an honest player: its input, the highest-rank vote certificate it retains, and the
snapshot `Q^r_i` recorded at the start of the current iteration's status round, whose rank is `h^r_i`. -/
structure PSt (n : ℕ) (Val : Type) where
  inp : Val
  best : VC n Val
  snap : VC n Val

/-- A conditional multicast: the eligibility label is `(ty, iter)` with the tag of `val`; `msg` is multicast if
the test succeeds; `terminal` marks the terminal action, after which the player decides `val` and halts. -/
structure Action (n : ℕ) (Val : Type) where
  ty : MType
  iter : ℕ
  val : Val
  msg : SMsg n Val
  terminal : Bool

section Honest

variable {n : ℕ} {Val : Type} [DecidableEq Val]

/-- The accepted votes of iteration `r`: signer, value, attached proposal. -/
def votesOf (acc : List (SMsg n Val)) (r : ℕ) : List (Fin n × Val × Option (Fin n × VC n Val)) :=
  acc.filterMap fun m =>
    match m with
    | SMsg.vote j r' b p => if r' = r then some (j, b, p) else none
    | _ => none

/-- The vote certificates of rank `r` a player assembles from the accepted votes of iteration `r`, one for each
value with `k` distinct signers (§10.2, p.38). For `r ≥ 2` the certificate takes the attached proposal of one of
these votes, chosen by the fixed order. -/
def assembleV (T : Ties n Val) (k r : ℕ) (acc : List (SMsg n Val)) : List (VC n Val) :=
  let vs := votesOf acc r
  (vs.map fun v => v.2.1).dedup.filterMap fun b =>
    let signers := ((vs.filter fun v => decide (v.2.1 = b)).map fun v => v.1).dedup
    if k ≤ signers.length then
      if r = 1 then some (VC.first b signers)
      else
        (pickMin T.prop ((vs.filter fun v => decide (v.2.1 = b)).filterMap fun v => v.2.2)).map
          fun p => VC.next r b signers p.1 p.2
    else none

/-- The commit certificates for iteration `r` a player assembles from the accepted commits (§10.2, p.38), one for
each value with `k` distinct signers, with the vote certificate of one of these commits. -/
def assembleC (T : Ties n Val) (k r : ℕ) (acc : List (SMsg n Val)) : List (CC n Val) :=
  let cs : List (Fin n × Val × VC n Val) := acc.filterMap fun m =>
    match m with
    | SMsg.commit j r' b vc => if r' = r then some (j, b, vc) else none
    | _ => none
  (cs.map fun c => c.2.1).dedup.filterMap fun b =>
    let signers := ((cs.filter fun c => decide (c.2.1 = b)).map fun c => c.1).dedup
    if k ≤ signers.length then
      (pickMin T.vc ((cs.filter fun c => decide (c.2.1 = b)).map fun c => c.2.2)).map
        fun vc => ⟨r, b, signers, vc⟩
    else none

/-- The commit certificates a player obtains at the delivery boundary of round `now`: those carried by accepted
termination messages and, after a commit round, those it assembles. -/
def obtainedCC (T : Ties n Val) (k V now : ℕ) (inbox : List (SMsg n Val)) : List (CC n Val) :=
  let acc := inbox.filter (accepts k V now)
  (acc.filterMap fun m =>
    match m with
    | SMsg.terminate _ _ cc => some cc
    | _ => none) ++
  (if phaseOf now = 3 ∧ 1 ≤ now ∧ now ≤ 4 * V + 2 then assembleC T k (iterOf now) acc else [])

/-- The action of the honest player `i` in round `R` (`1 ≤ R ≤ 4V + 3`), given the messages delivered to it in
round `R − 1` (§10.2, p.39).

It first processes the accepted messages: it retains the highest-rank vote certificate among its own, those
carried by accepted messages and those it assembles after a vote round. "If it obtains a valid commit
certificate, it selects one deterministically and performs its terminal action in the next round, in place of
that round's ordinary action": the action is the terminal test and multicast of `(Terminate, b)` with that
certificate. Otherwise, in an ordinary round:

* status: it records its current highest certificate as its snapshot and conditionally multicasts it;
* propose: it conditionally multicasts a proposal for the value of its highest certificate, with that
  certificate;
* vote, iteration `1`: it conditionally multicasts a vote for its input;
* vote, iteration `r ≥ 2`: it "chooses one valid proposal delivered in the propose round, preferring higher
  supporting-certificate rank", and conditionally multicasts a vote for its value "precisely when u ≥ h^r_i";
* commit: it conditionally multicasts a commit for `b` "if it received a rank-r vote certificate for b and no
  valid iteration-r vote for another value".

"Round 4V + 3 permits terminal actions only." -/
def hstep (T : Ties n Val) (k V : ℕ) (i : Fin n) (R : ℕ) (st : PSt n Val) (inbox : List (SMsg n Val)) :
    PSt n Val × Option (Action n Val) :=
  let now := R - 1
  let acc := inbox.filter (accepts k V now)
  let newV := if phaseOf now = 2 ∧ 1 ≤ now ∧ now ≤ 4 * V + 2 then assembleV T k (iterOf now) acc else []
  let st₁ : PSt n Val :=
    { st with best := (pickBest T (st.best :: (acc.flatMap SMsg.certs ++ newV))).getD st.best }
  match pickMin T.cc (obtainedCC T k V now inbox) with
  | some cc => (st₁, some ⟨MType.terminate, 0, cc.b, SMsg.terminate i cc.b cc, true⟩)
  | none =>
    if 4 * V + 2 < R then (st₁, none)
    else
      let r := iterOf R
      match phaseOf R with
      | 0 =>
        let st₂ : PSt n Val := { st₁ with snap := st₁.best }
        (st₂, some ⟨MType.status, r, st₂.snap.val, SMsg.status i r st₂.snap, false⟩)
      | 1 => (st₁, some ⟨MType.propose, r, st₁.best.val, SMsg.propose i r st₁.best.val st₁.best, false⟩)
      | 2 =>
        if r = 1 then (st₁, some ⟨MType.vote, 1, st₁.inp, SMsg.vote i 1 st₁.inp none, false⟩)
        else
          let props : List (Fin n × VC n Val) := acc.filterMap fun m =>
            match m with
            | SMsg.propose p _ _ s => some (p, s)
            | _ => none
          let top := (props.map fun p => p.2.rank).foldl max 0
          match pickMin T.prop (props.filter fun p => decide (p.2.rank = top)) with
          | some p =>
            if st₁.snap.rank ≤ p.2.rank then
              (st₁, some ⟨MType.vote, r, p.2.val, SMsg.vote i r p.2.val (some p), false⟩)
            else (st₁, none)
          | none => (st₁, none)
      | _ =>
        match ((votesOf acc r).map fun v => v.2.1).dedup with
        | [b] =>
          match (newV.filter fun c => decide (c.val = b)).head? with
          | some vc => (st₁, some ⟨MType.commit, r, b, SMsg.commit i r b vc, false⟩)
          | none => (st₁, none)
        | _ => (st₁, none)

end Honest

/-- What the adversary observes (§10.1, p.37): on a corruption, the corrupted key's evaluations at every label
in every candidate domain, the player's state and the messages delivered to it ("After corruption the adversary
can evaluate that key on any input"); each honest eligibility test with its evaluation, also when it fails
("Already queried evaluations may be disclosed during or after the indivisible action, including failed
eligibility tests"); each honest multicast; and each round boundary. -/
inductive SObs (n q V : ℕ) (Val : Type) where
  | row (i : Fin n) (ys : Fin q → Label V → Fin n) (st : PSt n Val) (inbox : List (SMsg n Val))
  | tested (i : Fin n) (lab : Label V) (y : Fin n)
  | cast (i : Fin n) (m : SMsg n Val)
  | boundary (R : ℕ)

/-- One move of the adversary: new corruptions; messages `(from, to, message)` sent through corrupted
identities; the honest player to act next (`none`: any); and, during registration, the candidate domain it
selects once it stops corrupting. -/
structure SMove (n q : ℕ) (Val : Type) where
  corrupt : Finset (Fin n)
  inject : List (Fin n × Fin n × SMsg n Val)
  next : Option (Fin n)
  seed : Fin q

/-- An adaptive rushing adversary (§10.1, p.37): an arbitrary randomized stateful strategy. -/
structure SAdv (n q V : ℕ) (Val : Type) where
  σ : Type
  init : PMF σ
  step : σ → List (SObs n q V Val) → PMF (σ × SMove n q Val)

/-- A configuration of the execution.

* `seed`: the selected candidate domain. `corrupted`: the corrupted players.
* `st`, `active`, `acted`: each player's state, whether it has not halted, whether it has acted this round.
* `inbox i`: the messages delivered to `i` at the last boundary; `pending i`: those sent to it this round.
* `decision`: the decisions. `honestTok`: the cores multicast honestly (the "honestly generated" tokens of
  §10.3). `tested`: the labels tested by players while honest.
* `casts`: the number of honest multicasts. `authFail`: an authenticity failure has occurred.
* `doneAt`: the first round at whose end no uncorrupted player was active.
* `adv`, `obs`: the adversary's state and its pending observations. -/
structure SCfg (n q V : ℕ) (Val σ : Type) where
  seed : Fin q
  corrupted : Finset (Fin n)
  st : Fin n → PSt n Val
  active : Fin n → Bool
  acted : Fin n → Bool
  inbox : Fin n → List (SMsg n Val)
  pending : Fin n → List (SMsg n Val)
  decision : Fin n → Option Val
  honestTok : List (Token n Val)
  tested : List (Fin n × Label V)
  casts : ℕ
  authFail : Bool
  doneAt : Option ℕ
  adv : σ
  obs : List (SObs n q V Val)

section Exec

variable {n q V : ℕ} {Val σ : Type} [DecidableEq Val]

/-- The eligibility threshold of a message type (§10.1, p.38): "For each ordinary phase other than proposal,
eligibility has probability p = ℓ/n. Proposal eligibility has probability 1/n. Termination eligibility has
probability ℓ/n". An evaluation is uniform on `{0, …, n − 1}` and "eligibility [holds] precisely when Y is below
the threshold for its type". -/
def thr (ell : ℕ) : MType → ℕ
  | MType.propose => 1
  | _ => ell

/-- The label of a token under an alternative. -/
def labelOf (alt : Alt Val) (V : ℕ) (ty : MType) (iter : ℕ) (v : Val) : Label V :=
  (ty, ⟨iter % (V + 2), Nat.mod_lt _ (Nat.succ_pos _)⟩, alt.tag v)

namespace SCfg

/-- A token is authentic at the current point of the execution (§4.2, p.12; §10.1, pp.37–38): its signer is
eligible for its label in the selected domain ("a correct proof binds the key, input, and evaluation"), and
either the token was multicast honestly by its signer, or its signer is corrupted and, in the erasure
alternative, did not complete an eligibility action for that label while honest ("any data verifying for a
phase whose signing key was erased while its owner was honest were signed by that owner before the erasure,
even if the owner is subsequently corrupted"). -/
def legit (alt : Alt Val) (ell : ℕ) (Y : Fin q → Fin n → Label V → Fin n) (c : SCfg n q V Val σ)
    (τ : Token n Val) : Bool :=
  decide ((Y c.seed τ.signer (labelOf alt V τ.ty τ.iter τ.val)).val < thr ell τ.ty) &&
    (decide (τ ∈ c.honestTok) ||
      (decide (τ.signer ∈ c.corrupted) &&
        (!alt.erase || decide ((τ.signer, labelOf alt V τ.ty τ.iter τ.val) ∉ c.tested))))

/-- Whether some message that an honest player accepts among `inbox`, delivered in round `now`, contains a token
that is not authentic: the authenticity failure of §10.1, p.38 ("signature or eligibility-proof authenticity
fails"). Signatures and proofs are ideal: every token of a delivered message verifies, and a token that is not
authentic is a forgery. -/
def forged (alt : Alt Val) (ell k now : ℕ) (Y : Fin q → Fin n → Label V → Fin n) (c : SCfg n q V Val σ)
    (inbox : List (SMsg n Val)) : Bool :=
  (inbox.filter (accepts k V now)).any fun m => m.tokens.any fun τ => !c.legit alt ell Y τ

/-- Apply corruptions, within the budget `f` (§10.1, p.37: "at most f […] corruptions in total"); a move
exceeding the budget is ignored for its corruptions. Each corruption reveals the key's evaluations, the state
and the delivered messages. -/
def corruptAll (c : SCfg n q V Val σ) (f : ℕ) (Y : Fin q → Fin n → Label V → Fin n)
    (C : Finset (Fin n)) : SCfg n q V Val σ :=
  if (c.corrupted ∪ C).card ≤ f then
    ((List.finRange n).filter fun i => i ∈ C ∧ i ∉ c.corrupted).foldl
      (fun c i =>
        { c with
          corrupted := insert i c.corrupted
          obs := c.obs ++ [SObs.row i (fun j lab => Y j i lab) (c.st i) (c.inbox i)] })
      c
  else c

/-- Messages of the adversary, only through corrupted identities, delivered at the round's boundary. -/
def injectAll (c : SCfg n q V Val σ) (ms : List (Fin n × Fin n × SMsg n Val)) : SCfg n q V Val σ :=
  ms.foldl
    (fun c m =>
      if m.1 ∈ c.corrupted then
        { c with pending := Function.update c.pending m.2.1 (c.pending m.2.1 ++ [m.2.2]) }
      else c)
    c

/-- `i` can still act in this round. -/
def runnable (c : SCfg n q V Val σ) (i : Fin n) : Bool :=
  decide (i ∉ c.corrupted) && c.active i && !c.acted i

/-- The action of the honest player `i` in round `R`, as one indivisible step (§10.1, p.37: "An honest
eligibility evaluation, generation of its proof, and commitment of its resulting multicast form one indivisible
local action"). The player processes its delivered messages (an accepted token that is not authentic sets
`authFail`), and if its algorithm prescribes a message it evaluates its key at the label; the test is recorded
and disclosed; if the evaluation is below the threshold the message is multicast, to itself as well ("Its own
honestly generated vote and commit tokens are available locally […] without a network send to itself"). After a
terminal action the player decides and halts, "whether or not it was eligible". -/
def activate (alt : Alt Val) (T : Ties n Val) (ell k R : ℕ) (Y : Fin q → Fin n → Label V → Fin n)
    (c : SCfg n q V Val σ) (i : Fin n) : SCfg n q V Val σ :=
  let res := hstep T k V i R (c.st i) (c.inbox i)
  let c₁ : SCfg n q V Val σ :=
    { c with
      st := Function.update c.st i res.1
      acted := Function.update c.acted i true
      authFail := c.authFail || c.forged alt ell k (R - 1) Y (c.inbox i) }
  match res.2 with
  | none => c₁
  | some a =>
    let lab := labelOf alt V a.ty a.iter a.val
    let y := Y c.seed i lab
    let c₂ : SCfg n q V Val σ :=
      { c₁ with tested := (i, lab) :: c₁.tested, obs := c₁.obs ++ [SObs.tested i lab y] }
    let c₃ : SCfg n q V Val σ :=
      if y.val < thr ell a.ty then
        { c₂ with
          pending := fun j => c₂.pending j ++ [a.msg]
          honestTok := a.msg.core :: c₂.honestTok
          casts := c₂.casts + 1
          obs := c₂.obs ++ [SObs.cast i a.msg] }
      else c₂
    if a.terminal then
      { c₃ with
        decision := Function.update c₃.decision i (some a.val)
        active := Function.update c₃.active i false }
    else c₃

end SCfg

/-- One move of the online execution: the adversary sees its pending observations and decides. A move with a new
corruption hands control straight back. Otherwise the player it names acts if it can, else the least player that
can; if nobody can, the round ends (`true`). The adversary is rushing: it sees every honest multicast of the
round before it sends, and it orders and interleaves honest actions with its corruptions, but cannot split an
action or stall a player. -/
noncomputable def smove (alt : Alt Val) (T : Ties n Val) (f ell k R : ℕ)
    (Y : Fin q → Fin n → Label V → Fin n)
    (step : σ → List (SObs n q V Val) → PMF (σ × SMove n q Val)) (c : SCfg n q V Val σ) :
    PMF (SCfg n q V Val σ × Bool) :=
  (step c.adv c.obs).map fun ad =>
    let c₀ : SCfg n q V Val σ := { c with adv := ad.1, obs := [] }
    let c₁ := c₀.corruptAll f Y ad.2.corrupt
    let c₂ := c₁.injectAll ad.2.inject
    if c₁.corrupted ≠ c₀.corrupted then (c₂, false)
    else
      let chosen : Option (Fin n) :=
        match ad.2.next with
        | some i => if c₂.runnable i then some i else (List.finRange n).find? c₂.runnable
        | none => (List.finRange n).find? c₂.runnable
      match chosen with
      | some i => (c₂.activate alt T ell k R Y i, false)
      | none => (c₂, true)

/-- The moves of one round. The fuel `n + f + 1` is never exhausted. -/
noncomputable def smoves (alt : Alt Val) (T : Ties n Val) (f ell k R : ℕ)
    (Y : Fin q → Fin n → Label V → Fin n)
    (step : σ → List (SObs n q V Val) → PMF (σ × SMove n q Val)) :
    ℕ → SCfg n q V Val σ → PMF (SCfg n q V Val σ)
  | 0, c => PMF.pure c
  | fuel + 1, c =>
    (smove alt T f ell k R Y step c).bind fun cb =>
      if cb.2 then PMF.pure cb.1 else smoves alt T f ell k R Y step fuel cb.1

/-- The delivery boundary of round `R` (§10.1, p.37: "Messages sent during a synchronous round are delivered
before the next round"). -/
def sboundary (R : ℕ) (c : SCfg n q V Val σ) : SCfg n q V Val σ :=
  { c with
    inbox := c.pending
    pending := fun _ => []
    acted := fun _ => false
    doneAt := c.doneAt.orElse fun _ =>
      if ∀ i, i ∉ c.corrupted → c.active i = false then some R else none
    obs := c.obs ++ [SObs.boundary R] }

/-- Rounds `R + 1, …, R + m` of the online execution. -/
noncomputable def srounds (alt : Alt Val) (T : Ties n Val) (f ell k : ℕ)
    (Y : Fin q → Fin n → Label V → Fin n)
    (step : σ → List (SObs n q V Val) → PMF (σ × SMove n q Val)) :
    ℕ → ℕ → SCfg n q V Val σ → PMF (SCfg n q V Val σ)
  | 0, _, c => PMF.pure c
  | m + 1, R, c =>
    ((smoves alt T f ell k (R + 1) Y step (n + f + 1) c).map (sboundary (R + 1))).bind
      (srounds alt T f ell k Y step m (R + 1))

/-- The final delivery boundary (§10.2, p.39): "every still-active player processes the delivered messages and
decides a value from a valid commit certificate if one is available, or a fixed default value otherwise; it then
halts without another eligibility test or send." -/
def sfinal (alt : Alt Val) (T : Ties n Val) (ell k : ℕ) (v₀ : Val) (Y : Fin q → Fin n → Label V → Fin n)
    (c : SCfg n q V Val σ) : SCfg n q V Val σ :=
  { c with
    decision := fun i =>
      if i ∉ c.corrupted ∧ c.active i = true then
        some (((pickMin T.cc (obtainedCC T k V (4 * V + 3) (c.inbox i))).map fun cc => cc.b).getD v₀)
      else c.decision i
    active := fun i => if i ∉ c.corrupted then false else c.active i
    authFail := c.authFail ||
      (List.finRange n).any fun i =>
        decide (i ∉ c.corrupted ∧ c.active i = true) && c.forged alt ell k (4 * V + 3) Y (c.inbox i)
    doneAt := c.doneAt.orElse fun _ => some (4 * V + 3) }

/-- The registration phase (§10.1, p.37). There are `q` candidate domains, each with its own evaluations. The
adversary corrupts players, adaptively and within the budget, seeing the evaluations of each corrupted key in
every candidate domain ("The adversary may inspect its own evaluations in those domains before selecting the
published list"); the first move without a new corruption selects the domain. The result is the corrupt set, the
adversary's state and observations, and the selected domain. -/
noncomputable def sgrind (f : ℕ) (Y : Fin q → Fin n → Label V → Fin n) (st : Fin n → PSt n Val)
    (step : σ → List (SObs n q V Val) → PMF (σ × SMove n q Val)) :
    ℕ → Finset (Fin n) → σ → List (SObs n q V Val) →
      PMF (Finset (Fin n) × σ × List (SObs n q V Val) × Fin q)
  | 0, C, s, o => (step s o).map fun ad => (C, ad.1, [], ad.2.seed)
  | fuel + 1, C, s, o =>
    (step s o).bind fun ad =>
      if (C ∪ ad.2.corrupt).card ≤ f ∧ C ∪ ad.2.corrupt ≠ C then
        sgrind f Y st step fuel (C ∪ ad.2.corrupt) ad.1
          (((List.finRange n).filter fun i => i ∈ ad.2.corrupt ∧ i ∉ C).map fun i =>
            SObs.row i (fun j lab => Y j i lab) (st i) [])
      else PMF.pure (C, ad.1, [], ad.2.seed)

/-- The whole execution of the protocol of §10.2 in the model of §10.1, with `n` players, corruption budget `f`,
committee parameter `ℓ` (`ell`), `V` ordinary iterations, `q` candidate domains, default value `v₀`, inputs `x`
and adversary `A`; the certificate threshold is `k = ℓ/2`.

The evaluations `Y j i lab` of key `i` at label `lab` in candidate domain `j` are independent and uniform on
`{0, …, n − 1}` ("each registered key has independent random evaluations at distinct inputs, including keys held
by the adversary"; "a new candidate has fresh independent evaluation tables"). After the registration phase, the
rounds `1, …, 4V + 3` run, and then the final boundary.

**Formalization Note.** An evaluation is "normalize[d] to a uniform Y ∈ [0, 1]" in the source; here it is uniform on
the grid `{0, 1/n, …, (n − 1)/n}`, which gives eligibility the exact probabilities `ℓ/n` and `1/n`. Only the labels
of the protocol are evaluated. -/
noncomputable def sexec [NeZero n] (alt : Alt Val) (T : Ties n Val) (f ell : ℕ) (v₀ : Val)
    (x : Fin n → Val) (A : SAdv n q V Val) : PMF (SCfg n q V Val A.σ) :=
  (PMF.uniformOfFintype (Fin q → Fin n → Label V → Fin n)).bind fun Y =>
    A.init.bind fun s₀ =>
      let st : Fin n → PSt n Val := fun i => ⟨x i, VC.zero (x i), VC.zero (x i)⟩
      (sgrind f Y st A.step f ∅ s₀ []).bind fun g =>
        let c₀ : SCfg n q V Val A.σ :=
          { seed := g.2.2.2
            corrupted := g.1
            st := st
            active := fun _ => true
            acted := fun _ => false
            inbox := fun _ => []
            pending := fun _ => []
            decision := fun _ => none
            honestTok := []
            tested := []
            casts := 0
            authFail := false
            doneAt := none
            adv := g.2.1
            obs := g.2.2.1 }
        (srounds alt T f ell (ell / 2) Y A.step (4 * V + 3) 0 c₀).map
          (sfinal alt T ell (ell / 2) v₀ Y)

end Exec

section Measures

variable {n q V : ℕ} {Val σ : Type}

/-- `T` of Theorem 9: "the time by which no honest player remains active", in rounds. -/
def SCfg.time (ω : SCfg n q V Val σ) : ℕ := ω.doneAt.getD (4 * V + 3)

/-- `M` of Theorem 9: "the number of point-to-point messages sent while their senders are honest, including all
terminal messages". A multicast "delivers the same message to every other player" and costs `n − 1`. -/
def SCfg.msgs (ω : SCfg n q V Val σ) : ℕ := ω.casts * (n - 1)

/-- Agreement and strong unanimity (§10.1, p.37): "Agreement means that all forever-honest decisions coincide;
strong unanimity means that if all forever-honest inputs equal b, all their decisions equal b." -/
def SCfg.Correct (x : Fin n → Val) (ω : SCfg n q V Val σ) : Prop :=
  (∀ i j, i ∉ ω.corrupted → j ∉ ω.corrupted → ∀ b b', ω.decision i = some b →
    ω.decision j = some b' → b = b') ∧
  (∀ b, (∀ i, i ∉ ω.corrupted → x i = b) → ∀ i, i ∉ ω.corrupted → ∀ b',
    ω.decision i = some b' → b' = b)

end Measures

end BeyondDS.Supplement


