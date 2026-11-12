-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_ProofCreation
-- name    : SubcubicBA_PlainPKI_ProofCreation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:44:55.8526+00:00
-- url     : https://prove2.me/theorems/656ded63-eed6-4321-847b-5e46420ff4e2
-- title:
--   ProofCreation with GetAccusations (CakeLeader, CakeHelper), SpreadVotes and ComputeProof
-- statement:
--   ProofCreation of §7, written out round by round as a protocol of the execution model. It is parametrized by a disperser family $G_1$, a fault-tolerant expander family $G_2$, a SpreadVotes length $\rho(n)$ and the paper's arbitrary choices.
--
--   1. **Votes.** Round $0$: send the signed vote $\mathrm{Vote}(p,v_{in})$ to everyone. Round $1$: if fewer than $t+1$ valid votes for $0$ and fewer than $t+1$ for $1$ arrived, set $v_{in}\leftarrow\bot$, then send the signed vote again. *Accusers* are the parties that voted $0$ or $1$ in round 1; *Accused* are the parties that sent no valid vote in round 1; *Votes* are the valid votes received in rounds 0 and 1.
--   2. **GetAccusations.** Round $2$: send $|\mathit{Accused}|$. $A$ is the set of accusers announcing at least $3n/10$. If $|A|\le3n/10$ the party runs CakeLeader$(A,1,n)$, and it always serves as CakeHelper for every leader. The recursion runs in lock step over $\lceil\log_2n\rceil+1$ levels:
--      - at level $d$ the leader queries in round $3+2d$, sending $(\mathrm{Accuse},l,r)$ to a single remaining member or $(\mathrm{SPLIT},l,r,\lceil|A'|/2\rceil)$ to every member of a branch $(A',l,r)$;
--      - helpers answer in round $4+2d$: at most $\lceil\log_2n\rceil$ split answers (the $i$-th party of $\mathit{Accused}\cap\{p_l,\dots,p_r\}$, or $0$) and at most one signed accusation, after which the helper stays silent;
--      - the leader splits $A'$ into the $\lceil|A'|/2\rceil$ members with lowest answers $A_l$ (ties broken arbitrarily) and the rest, with ranges $[l,m]$ and $[m+1,r]$, where $m=\max_{A_l}a_q$.
--   3. **SpreadVotes.** In round $sv_0=3+2(\lceil\log_2n\rceil+1)$ the vote of each $q$ in *Votes* is sent to $N_{G_1}(q)$ and all of *Votes* to $N_{G_2}(p)$. During the next $\rho(n)$ rounds every newly received valid vote is forwarded to $N_{G_2}(p)$ and added.
--   4. **ComputeProof.** In round $sv_0+\rho(n)+1$ the party tries $b=0$ and then $b=1$. $Q$ is the set of parties with a vote for $b$ or $\bot$; $E$ is the set of collected accusations disjoint from $Q$; $M$ is a maximum matching of $E$. If $|Q|\ge1$ and $|Q|+|M|\ge t+1$, the party outputs $t+1$ votes of $Q$ and accusations of $M$ with at least one vote, as a proof message; otherwise it outputs $\bot$.
--
--   This is the protocol of Theorem 4.
--
--   **Formalization Note** Every arbitrary choice of the paper is a field of `PCChoice`: tie breaking, the helper's accused party, the maximum matching, the vote per party and the final selection. An invalid choice is replaced by a fixed valid one, so the theorem quantifies over all valid choices. The query $(\mathrm{SPLIT},l,m,\cdot)$ of the pseudocode is read as $(\mathrm{SPLIT},l,r,\cdot)$, since $m$ is not yet defined there. *Votes* includes the first-round votes, a correction of the pseudocode (which keeps only the second round): the proof of Theorem 4 forms proofs from first-round votes in its first case, and without them Theorem 4 fails (see that item).
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §7.2–7.5 (pp. 13–19): ProofCreation, GetAccusations, CakeHelper, CakeLeader, SpreadVotes, ComputeProof

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs
import Definitions.Def_SubcubicBA_PlainPKI_CommitteeBroadcast

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # ProofCreation (§7, pp. 12–20) as a protocol of the execution model

Party `p` (index `I.self`, `n = I.n`, `t = I.t`, session `I.session`), with input bit `v_in`:

* Round 0: send the signed vote `(Vote(p, v_in), σ)` to everyone.
* Round 1: if fewer than `t+1` valid votes for `0` and fewer than `t+1` for `1` were received
  (one per channel, the vote of the channel's party), set `v_in ← ⊥`; send the signed vote again.
  `Accusers` = parties that sent a vote for `0` or `1` in this round; `Accused` = parties that
  sent no valid vote in this round. `Votes` = the valid votes received in rounds 0 and 1
  (correction of the pseudocode, which keeps only round 1: the proof of Theorem 4 forms proofs
  from first-round votes when `nb_⊥ ≤ 4n/10`).
* GetAccusations (rounds `2, …, 2+2D`, `D = ⌈log₂ n⌉ + 1`): round 2, send `|Accused|`; `A` = the
  accusers announcing at least `3n/10`; if `|A| ≤ 3n/10` the party leads CakeLeader(A, 1, n),
  and in every case it acts as CakeHelper(p_i, Accused) for every leader `p_i`. The recursion of
  CakeLeader runs in lock step: at level `d` the leader sends its queries in round `3+2d` (for a
  branch `(A', l, r)`: `(Accuse, l, r)` to the single member if `|A'| = 1`, else
  `(SPLIT, l, r, ⌈|A'|/2⌉)` to every member) and the helpers answer in round `4+2d`. On the
  answers `a_q` (`0` if none), `A_l` = the `⌈|A'|/2⌉` members with lowest `a_q` (ties broken by
  the arbitrary key `prio`), `m = max_{q ∈ A_l} a_q`, and the branch splits into `(A_l, l, m)`
  and `(A' \ A_l, m+1, r)`. A helper answers at most `⌈log₂ n⌉` split queries of a leader with
  the index of the `i`-th party of `Accused ∩ {p_l, …, p_r}` (or `0`), and at most one
  accusation query, with a signed `Accusation(p, p_j)` for some (arbitrary) `p_j` in
  `Accused ∩ {p_l, …, p_r}` if there is one; after an accusation query it stays silent for that
  leader. Party numbers in queries and answers are `1, …, n` (`p_x` is index `x - 1`).
* SpreadVotes (rounds `sv₀ = 3+2D, …, sv₀+ρ`): in round `sv₀` the vote of each party `q` in
  `Votes` is sent to `N_{G₁}(q)` and all of `Votes` to `N_{G₂}(p)`; in each of the next `ρ`
  rounds, every newly received valid vote not yet in `Votes` is forwarded to `N_{G₂}(p)` and added;
  votes received in round `sv₀ + ρ` are added at the end.
* Round `sv₀+ρ+1`: ComputeProof(0, …) and then ComputeProof(1, …): `Q` = the parties with a vote
  for `b` or `⊥` (one vote per party, chosen arbitrarily), `E` = the accusations disjoint from
  `Q`, `M` an (arbitrary) maximum matching of `E`; if `|Q| ≥ 1` and `|Q| + |M| ≥ t+1`, return an
  (arbitrary) set of `t+1` votes of `Q` and accusations of `M` with at least one vote; else `⊥`.
  The output is `opt (some proof)` or `opt none`.

Every arbitrary choice of the paper is a field of `PCChoice`; an invalid choice is replaced by a
fixed valid one, so every valid choice is realized by some `PCChoice`. -/

/-- The arbitrary choices of ProofCreation. -/
structure PCChoice where
  /-- tie-breaking key of CakeLeader: leader, level, party -/
  prio : ℕ → ℕ → ℕ → ℕ
  /-- CakeHelper's accused party: helper, leader, candidates -/
  accPick : ℕ → ℕ → List ℕ → ℕ
  /-- ComputeProof's vote of a party in `Q`: party, `b`, voter, number of candidate votes -/
  votePick : ℕ → ℕ → ℕ → ℕ → ℕ
  /-- ComputeProof's maximum matching: party, `b`, `E` -/
  mm : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  /-- ComputeProof's selected votes and accusations: party, `b`, `Q` resp. `M` -/
  selQ : ℕ → ℕ → List ℕ → List ℕ
  selM : ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)

/-- The signed-vote item expression of the party itself. -/
def voteItemE (p v : ℕ) : Expr :=
  let d : Expr := .pair (.nat 0) (.pair (.nat p) (.nat v))
  .pair d (.signSelf [] d)

/-- The signed-accusation item expression of the party itself. -/
def accItemE (p c : ℕ) : Expr :=
  let d : Expr := .pair (.nat 1) (.pair (.nat p) (.nat c))
  .pair d (.signSelf [] d)

/-- If `e` is a valid signed vote of a party `q < n` for `v ≤ 2` (session `sess`), its data. -/
def voteOf (o : Obs) (sess n : ℕ) (e : Expr) : Option (ℕ × ℕ) :=
  match o.shape e with
  | some (.pair (.pair (.nat 0) (.pair (.nat q) (.nat v))) .tok) =>
      if q < n ∧ v ≤ 2 ∧ o.test (.isSig q sess (.fst e) (.snd e)) = true then some (q, v) else none
  | _ => none

/-- If `e` is a valid signed accusation `(a, c)` with `a, c < n`, its data. -/
def accOf (o : Obs) (sess n : ℕ) (e : Expr) : Option (ℕ × ℕ) :=
  match o.shape e with
  | some (.pair (.pair (.nat 1) (.pair (.nat a) (.nat c))) .tok) =>
      if a < n ∧ c < n ∧ o.test (.isSig a sess (.fst e) (.snd e)) = true then some (a, c) else none
  | _ => none

/-- Number of CakeLeader levels. -/
def pcLevels (n : ℕ) : ℕ := Nat.clog 2 n + 1

/-- First round of SpreadVotes. -/
def pcSV (n : ℕ) : ℕ := 3 + 2 * pcLevels n

noncomputable section
variable (o : Obs) (I : LocalInit)

/-- The input bit (`nat 1 ↦ 1`, anything else `↦ 0`). -/
def pcVin : ℕ := if o.shape .input = some (.nat 1) then 1 else 0

/-- Valid round-0 votes for `v` (channel `q` carrying `q`'s vote). -/
def pcCount1 (v : ℕ) : ℕ :=
  ((List.range I.n).filter fun q => decide (voteOf o I.session I.n (.recv 0 q) = some (q, v))).length

/-- The second-round vote value. -/
def pcVin2 : ℕ :=
  if I.t + 1 ≤ pcCount1 o I 0 ∨ I.t + 1 ≤ pcCount1 o I 1 then pcVin o else 2

/-- `Votes`: the valid votes received in round 1, as `(voter, value, item)`. -/
def pcVotes2 : List (ℕ × ℕ × Expr) :=
  (List.range I.n).filterMap fun q =>
    match voteOf o I.session I.n (.recv 1 q) with
    | some (q', v) => if q' = q then some (q, v, .recv 1 q) else none
    | none => none

/-- The valid votes received in round 0 (channel `q` carrying `q`'s vote). -/
def pcVotes1 : List (ℕ × ℕ × Expr) :=
  (List.range I.n).filterMap fun q =>
    match voteOf o I.session I.n (.recv 0 q) with
    | some (q', v) => if q' = q then some (q, v, .recv 0 q) else none
    | none => none

/-- `Votes` as used by SpreadVotes and ComputeProof: the valid votes received in both voting
rounds (correction: the pseudocode keeps only the second round, but the proof of Theorem 4,
case `nb_⊥ ≤ 4n/10`, forms proofs from first-round votes). -/
def pcVotesAll : List (ℕ × ℕ × Expr) :=
  pcVotes2 o I ++ (pcVotes1 o I).filter fun x => !((pcVotes2 o I).any fun y => o.eqB y.2.2 x.2.2)

/-- `Accused`: parties without a valid vote in round 1. -/
def pcAccused : List ℕ :=
  (List.range I.n).filter fun q => ((pcVotes2 o I).find? fun x => x.1 = q).isNone

/-- `A`: accusers (vote for 0 or 1 in round 1) announcing at least `3n/10` accused parties. -/
def pcA : List ℕ :=
  (List.range I.n).filter fun q =>
    ((pcVotes2 o I).any fun x => x.1 = q ∧ x.2.1 ≤ 1) &&
    (match o.shape (.recv 2 q) with
      | some (.nat k) => decide (3 * I.n ≤ 10 * k)
      | _ => false)

/-- A helper's answer at level `d` from party `q` (`0` unless a positive number). -/
def pcAns (d q : ℕ) : ℕ :=
  match o.shape (.recv (4 + 2 * d) q) with
  | some (.nat j) => j
  | _ => 0

/-- Lexicographic order on keys. -/
def lexLe (x y : ℕ × ℕ × ℕ) : Bool :=
  decide (x.1 < y.1 ∨ (x.1 = y.1 ∧ (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 ≤ y.2.2))))

/-- One CakeLeader recursion step on a branch `(A', l, r)` at level `d`. -/
def pcSplit (ch : PCChoice) (d : ℕ) (br : List ℕ × ℕ × ℕ) : List (List ℕ × ℕ × ℕ) :=
  let A' := br.1
  if A'.length ≤ 1 then []
  else
    let h := (A'.length + 1) / 2
    let key (q : ℕ) : ℕ × ℕ × ℕ := (pcAns o d q, ch.prio I.self d q, q)
    let sorted := A'.mergeSort fun a b => lexLe (key a) (key b)
    let Al := sorted.take h
    let m := (Al.map (pcAns o d)).foldl max 0
    [(Al, br.2.1, m), (sorted.drop h, m + 1, br.2.2)]

/-- CakeLeader branches active at level `d`. -/
def pcBranches (ch : PCChoice) : ℕ → List (List ℕ × ℕ × ℕ)
  | 0 => if 10 * (pcA o I).length ≤ 3 * I.n then [(pcA o I, 1, I.n)] else []
  | d + 1 => (pcBranches ch d).flatMap (pcSplit o I ch d)

/-- The leader's query to party `j` at level `d`. -/
def pcQuery (ch : PCChoice) (d j : ℕ) : Option Expr :=
  match (pcBranches o I ch d).find? fun br => br.1.contains j with
  | some (A', l, r) =>
      if A'.length = 1 then some (.pair (.nat 3) (.pair (.nat l) (.nat r)))
      else some (.pair (.nat 2) (.pair (.nat l) (.pair (.nat r) (.nat ((A'.length + 1) / 2)))))
  | none => none

/-- The accusations the leader collected (CakeLeader's result `M`), as `(a, c, item)`. -/
def pcAccs (ch : PCChoice) : List (ℕ × ℕ × Expr) :=
  (List.range (pcLevels I.n)).flatMap fun d =>
    (pcBranches o I ch d).filterMap fun br =>
      match br.1 with
      | [q] =>
          match accOf o I.session I.n (.recv (4 + 2 * d) q) with
          | some (a, c) => if a = q then some (a, c, .recv (4 + 2 * d) q) else none
          | none => none
      | _ => none

/-- The split query received from leader `i` at level `d`. -/
def pcSplitQ (d i : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match o.shape (.recv (3 + 2 * d) i) with
  | some (.pair (.nat 2) (.pair (.nat l) (.pair (.nat r) (.nat x)))) => some (l, r, x)
  | _ => none

/-- The accusation query received from leader `i` at level `d`. -/
def pcAccQ (d i : ℕ) : Option (ℕ × ℕ) :=
  match o.shape (.recv (3 + 2 * d) i) with
  | some (.pair (.nat 3) (.pair (.nat l) (.nat r))) => some (l, r)
  | _ => none

/-- CakeHelper's answer to leader `i` at level `d`. -/
def pcHelp (ch : PCChoice) (d i : ℕ) : Option Expr :=
  let B := pcAccused o I
  let silenced := (List.range d).any fun d' => (pcAccQ o d' i).isSome
  let nSplits := ((List.range d).filter fun d' => (pcSplitQ o d' i).isSome).length
  let inRange (l r x : ℕ) : Bool := decide (l ≤ x + 1 ∧ x + 1 ≤ r)
  if silenced then none
  else
    match pcSplitQ o d i, pcAccQ o d i with
    | some (l, r, x), _ =>
        if nSplits < Nat.clog 2 I.n then
          let Q := B.filter (inRange l r)
          some (.nat (if 1 ≤ x ∧ x ≤ Q.length then Q.getD (x - 1) 0 + 1 else 0))
        else none
    | none, some (l, r) =>
        let cand := B.filter (inRange l r)
        if cand = [] then none
        else
          let c := if cand.contains (ch.accPick I.self i cand) then ch.accPick I.self i cand
            else cand.headD 0
          some (accItemE I.self c)
    | none, none => none

/-- The data of the items in a received list message. -/
def pcListItems (e : Expr) : List Expr :=
  (List.range (o.listLen e)).map fun k => e.nth k

/-- SpreadVotes: new valid votes received in round `x - 1`, not equal to any vote in `cur`. -/
def pcNew (x : ℕ) (cur : List (ℕ × ℕ × Expr)) : List (ℕ × ℕ × Expr) :=
  let recvd : List Expr := (List.range I.n).flatMap fun i => pcListItems o (.recv (x - 1) i)
  recvd.foldl (fun acc e =>
    match voteOf o I.session I.n e with
    | some (q, v) =>
        if (cur ++ acc).any (fun y => o.eqB y.2.2 e) then acc else acc ++ [(q, v, e)]
    | none => acc) []

/-- SpreadVotes: `Votes` after processing the receipts of rounds `< sv₀ + k + 1`. -/
def pcSVVotes : ℕ → List (ℕ × ℕ × Expr)
  | 0 => pcVotesAll o I
  | k + 1 => pcSVVotes k ++ pcNew o I (pcSV I.n + k + 1) (pcSVVotes k)

/-- Pairwise disjoint party sets. -/
def accMatchingB (M : List (ℕ × ℕ)) : Bool :=
  decide (M.Pairwise fun y y' => Disjoint ({y.1, y.2} : Finset ℕ) {y'.1, y'.2})

/-- ComputeProof(b, Votes, Accusations): the proof items, if a proof is found. -/
def pcCompute (ch : PCChoice) (b : ℕ) (votes accs : List (ℕ × ℕ × Expr)) : Option (List Expr) :=
  let Vb := votes.filter fun x => x.2.1 = b ∨ x.2.1 = 2
  let Qp := (Vb.map Prod.fst).dedup
  let voteFor (q : ℕ) : Expr :=
    let cs := Vb.filter fun x => x.1 = q
    let i := ch.votePick I.self b q cs.length
    ((cs.getD (if i < cs.length then i else 0) (0, 0, .bot))).2.2
  let E0 := accs.filter fun y => decide (y.1 ∉ Qp ∧ y.2.1 ∉ Qp)
  let E : List (ℕ × ℕ × Expr) :=
    E0.foldl (fun acc y => if acc.any (fun z => z.1 = y.1 ∧ z.2.1 = y.2.1) then acc else acc ++ [y]) []
  let Ed : List (ℕ × ℕ) := E.map fun y => (y.1, y.2.1)
  let ms := Ed.sublists.filter accMatchingB
  let maxLen := (ms.map List.length).foldl max 0
  let cand := ch.mm I.self b Ed
  let M : List (ℕ × ℕ) :=
    if decide (cand.Sublist Ed) && accMatchingB cand && decide (cand.length = maxLen) then cand
    else (ms.find? fun l => l.length = maxLen).getD []
  let accFor (y : ℕ × ℕ) : Expr := ((E.find? fun z => z.1 = y.1 ∧ z.2.1 = y.2).map fun z => z.2.2).getD .bot
  if 1 ≤ Qp.length ∧ I.t + 1 ≤ Qp.length + M.length then
    let sq := ch.selQ I.self b Qp
    let sm := ch.selM I.self b M
    let ok : Bool := decide (sq.Sublist Qp ∧ sm.Sublist M ∧ 1 ≤ sq.length ∧ sq.length + sm.length = I.t + 1)
    let kq := min Qp.length (I.t + 1)
    let sq' := if ok then sq else Qp.take kq
    let sm' := if ok then sm else M.take (I.t + 1 - kq)
    some (sq'.map voteFor ++ sm'.map accFor)
  else none

end

/-- ProofCreation with disperser family `G₁` (out-neighbourhoods), fault-tolerant expander family
`G₂`, SpreadVotes length `ρ n`, and arbitrary choices `ch`. -/
noncomputable def proofCreation (G₁ : (n : ℕ) → Fin n → Finset (Fin n))
    (G₂ : (n : ℕ) → SimpleGraph (Fin n)) (ρ : ℕ → ℕ) (ch : PCChoice) : Protocol where
  send I o j :=
    let n := I.n
    let sv := pcSV n
    let inG₁ (q : ℕ) : Prop := ∃ (hq : q < n) (hj : j < n), (⟨j, hj⟩ : Fin n) ∈ G₁ n ⟨q, hq⟩
    let inG₂ : Prop := ∃ (hp : I.self < n) (hj : j < n), (G₂ n).Adj ⟨I.self, hp⟩ ⟨j, hj⟩
    have : DecidablePred inG₁ := Classical.decPred _
    have : Decidable inG₂ := Classical.dec _
    if o.round = 0 then some (voteItemE I.self (pcVin o))
    else if o.round = 1 then some (voteItemE I.self (pcVin2 o I))
    else if o.round = 2 then some (.nat (pcAccused o I).length)
    else if o.round < sv then
      (if o.round % 2 = 1 then pcQuery o I ch ((o.round - 3) / 2) j
       else pcHelp o I ch ((o.round - 4) / 2) j)
    else if o.round = sv then
      let items := ((pcVotesAll o I).filter fun x => decide (inG₁ x.1)).map (fun x => x.2.2) ++
        (if inG₂ then (pcVotesAll o I).map (fun x => x.2.2) else [])
      if items = [] then none else some (listExpr items)
    else if o.round ≤ sv + ρ n then
      let k := o.round - sv - 1
      let new := pcNew o I o.round (pcSVVotes o I k)
      if inG₂ ∧ new ≠ [] then some (listExpr (new.map fun x => x.2.2)) else none
    else none
  decide I o :=
    let sv := pcSV I.n
    if o.round < sv + ρ I.n + 1 then none
    else
      let votes := pcSVVotes o I (ρ I.n + 1)
      let accs := pcAccs o I ch
      match pcCompute I ch 0 votes accs with
      | some items => some (.pair (.nat 1) (listExpr items))
      | none =>
          match pcCompute I ch 1 votes accs with
          | some items => some (.pair (.nat 1) (listExpr items))
          | none => some (.nat 0)

end SubcubicBA.PlainPKI


