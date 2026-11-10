-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol3
-- name    : ChoiSemiHonestMPC_OTUpper_Protocol3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:31:14.071017+00:00
-- url     : https://prove2.me/theorems/f3508620-3002-4643-8875-a09d5bde258e
-- title:
--   Protocol 3 (Figure 7) with the parameters of Section 7.1, and one trial's table
-- statement:
--   Here $s=2\lceil 4/(1-2\alpha)^2\rceil$, tags take $2^{\lceil\log_2(s(s-1))\rceil}$ values (counted from 0), and there are $T=32K$ trials with independent randomness. Step 1 executes trial $j$ in round $2j$, with a redundant idle barrier in round $2j+1$; request receipt, local draws and replies may interleave within the trial. Every server draws a uniform bit, a uniform tag and a volunteer flag with probability $1/(n-s+1)$. Bob draws a uniform ordered tuple of $s-1$ distinct servers and sends REQUEST to each, and each requested server returns its tagged bit to Bob. Step 2, round $2T$: every server erases everything except, for each trial, its participation flag (requested or volunteered) and tagged bit. Step 3: in round $2T+1+j$ every participating server sends its tagged bit to Alice. In round $3T+1$ every server erases the rest and stops. Step 4, round $3T+2$: Alice accepts the trials with exactly $s$ tagged bits with distinct tags. With fewer than $K$ accepted she announces abort; otherwise she sends the $T$-bit selection vector of the first $K$ accepted trials and their tags in increasing order. Step 5, round $3T+3+k$ for selected trial $k$: the clients sample and exchange uniform permutations $\pi_A,\pi_B$, sequentially in selected-trial order. The $r$-th tag moves to position $\pi_B(\pi_A(r))$. Alice outputs $U_j=\bigoplus_{q\text{ in half }j}Z'_q$; Bob outputs $C=1-\lfloor T/(s/2)\rfloor$ (positions from 0) and $U_C$. `p3TrialRaw` is one trial's raw randomness, from the same draws. `p3Accept` is acceptance. `p3Labeling` places participants by increasing tag, then nonparticipants in the independent uniform order $\rho$. `p3Table` gives the rows (status, volunteer flag, tag, bit), where status $k\ge1$ means the $k$-th entry of Bob's tuple. `p3AcceptedTableLaw` is the explicit distribution described in Lemma 7.2.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Sections 7.1, 7.3 and Figure 7, p. 31–33 (PDF 33–35)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol1

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-! ### Protocol 3 parameters (Section 7.1) -/

/-- `s = 2 ⌈4 / (1 - 2α)^2⌉`: tagged bits per accepted trial. -/
def s3 (α : ℝ) : ℕ := 2 * ⌈4 / (1 - 2 * α) ^ 2⌉₊

/-- Tag width `⌈log₂ (s(s-1))⌉`: tags range over `2 ^ tagW s` values (the paper's
`{1, …, 2^{⌈log₂(s(s-1))⌉}}`, shifted to `{0, …, 2^{⌈log₂(s(s-1))⌉} - 1}`). -/
def tagW (s : ℕ) : ℕ := Nat.clog 2 (s * (s - 1))

/-- One server's draw in one trial: a uniform bit `Z_i`, a uniform tag `L_i`, and the
volunteer flag (probability `1/(n - s + 1)`). -/
def p3Draw (n s : ℕ) : PMF (Bool × ℕ × Bool) :=
  unifBit.bind fun z =>
    (PMF.uniformOfFintype (Fin (2 ^ tagW s))).bind fun l =>
      (bern (1 / ((n : ℝ) - s + 1))).map fun v => (z, l.1, v)

/-- Bob's uniform ordered tuple of `s - 1` distinct servers (as a list of labels). -/
def p3Tuple (n s : ℕ) : PMF (List ℕ) :=
  if h : s - 1 ≤ n then
    haveI : Nonempty (Fin (s - 1) ↪ Fin n) := ⟨Fin.castLEEmb h⟩
    (PMF.uniformOfFintype (Fin (s - 1) ↪ Fin n)).map fun e =>
      (List.finRange (s - 1)).map fun k => (e k).1
  else PMF.pure []

/-- `K` uniform permutations of `{0, …, s-1}`, each as the list of its values. -/
def p3Perms (K s : ℕ) : PMF (List (List ℕ)) :=
  (PMF.uniformOfFintype (Fin K → Equiv.Perm (Fin s))).map fun f =>
    (List.finRange K).map fun k => (List.finRange s).map fun r => (f k r).1

/-- Private state of a party in Protocol 3.  Servers: `draw j` = `(Z, L, volunteer)` in
trial `j`; after the first erasure only `part j` = `(participation flag, Z, L)` remains,
after the second nothing (`stage` counts erasures).  Bob: `tuple j` = his requested servers
in trial `j`.  Clients: `perm k` = their permutation share for selected trial `k`. -/
structure P3State (n : ℕ) where
  draw : ℕ → Option (Bool × ℕ × Bool) := fun _ => none
  part : ℕ → Option (Bool × Bool × ℕ) := fun _ => none
  stage : ℕ := 0
  sentTo : List (ℕ × Party n) := []
  inbox : List (ℕ × Party n × Msg) := []
  tuple : ℕ → Option (List ℕ) := fun _ => none
  perm : ℕ → Option (List ℕ) := fun _ => none

namespace P3State

variable {n : ℕ}

/-- The message received from `q` in round `r`. -/
def msgAt (s : P3State n) (r : ℕ) (q : Party n) : Option Msg :=
  (s.inbox.find? fun e => decide (e.1 = r ∧ e.2.1 = q)).map fun e => e.2.2

/-- Messages received from servers in round `r`, decoded as (bit, tag). -/
def taggedAt (s : P3State n) (_w r : ℕ) : List (Bool × ℕ) :=
  (s.inbox.filter fun e => decide (e.1 = r) && !e.2.1.isClient).map fun e =>
    (e.2.2.headD false, decNat (e.2.2.drop 1))

/-- Already sent to `q` in round `r`? -/
def didSend (s : P3State n) (r : ℕ) (q : Party n) : Bool := decide ((r, q) ∈ s.sentTo)

/-- Record a send. -/
def markSent (s : P3State n) (r : ℕ) (q : Party n) : P3State n :=
  { s with sentTo := s.sentTo ++ [(r, q)] }

end P3State

/-- Alice's accepted trials: exactly `s` tagged bits with distinct tags arrived in the
trial's round of step 3 (round `2T + 1 + j` for trial `j`, `T = 32K`). -/
def p3Accepted {n : ℕ} (s T w : ℕ) (st : P3State n) : List ℕ :=
  (List.range T).filter fun j =>
    let l := st.taggedAt w (2 * T + 1 + j)
    decide (l.length = s ∧ (l.map Prod.snd).Nodup)

/-- Sort a list of numbers increasingly. -/
def sortNat (l : List ℕ) : List ℕ := l.mergeSort fun a b => decide (a ≤ b)

/-- **Protocol 3, general version (Figure 7)**, `T = 32K` trials.  Step 1, trial `j`
(round `2j`, followed by an idle barrier round `2j+1`): every server draws `(Z_i, L_i, volunteer)`; Bob draws a uniform
ordered `(s-1)`-tuple of distinct servers and sends "REQUEST" (`[true]`) to each; each
requested server returns `(Z_i, L_i)` to Bob.  Step 2 (round `2T`): every server erases all
but its participation flag (requested or volunteered) and tagged bit for each trial.
Step 3 (round `2T+1+j` for trial `j`): every participating server sends its tagged bit to
Alice; round `3T+1`: every server erases the rest and stops.  Step 4 (round `3T+2`): Alice
accepts the trials with exactly `s` tagged bits with distinct tags; with fewer than `K` she
announces abort (`[false]`), else she sends the `T`-bit selection vector of the first `K`
accepted trials and, for each, its tags in increasing order.  Step 5 (round `3T+3+k` for selected trial `k`): both
clients sample and exchange uniform permutations `π_A, π_B`, sequentially by trial; the `r`-th
tag (increasing order) moves to position `π_B(π_A(r))`; Alice outputs
`U_j = ⊕_{q in half j} Z'_q`, Bob `C = 1 - ⌊T/(s/2)⌋` (positions from `0`) and `U_C`. -/
def protocol3 (α : ℝ) (n K : ℕ) :
    Protocol n Unit Unit (Bits K × Bits K) (Bits K × Bits K) where
  S := P3State n
  initA _ := {}
  initB _ := {}
  initS _ := {}
  rounds := 3 * (32 * K) + 3 + K
  opBound := 2 * n + 2 * s3 α + 8
  act p r st :=
    let s := s3 α
    let T := 32 * K
    let w := tagW s
    match p with
    | .server _ =>
      if r < 2 * T then
        let j := r / 2
        if r % 2 = 0 then
          match st.draw j with
          | none => some (.compute ((p3Draw n s).map fun x =>
              { st with draw := Function.update st.draw j (some x) }))
          | some (z, l, _) =>
            if (st.msgAt r .bob).isSome && !st.didSend r .bob then
              some (.send .bob (z :: encNat w l) (st.markSent r .bob))
            else none
        else none
      else if r = 2 * T then
        if st.stage = 0 then
          some (.compute (PMF.pure
            { stage := 1
              part := fun j =>
                if j < T then
                  match st.draw j with
                  | some (z, l, v) => some (v || (st.msgAt (2 * j) .bob).isSome, z, l)
                  | none => none
                else none }))
        else none
      else if r < 3 * T + 1 then
        let j := r - (2 * T + 1)
        match st.part j, st.didSend r .alice with
        | some (true, z, l), false => some (.send .alice (z :: encNat w l) (st.markSent r .alice))
        | _, _ => none
      else if r = 3 * T + 1 ∧ st.stage = 1 then some (.compute (PMF.pure { stage := 2 }))
      else none
    | .bob =>
      if r < 2 * T ∧ r % 2 = 0 then
        let j := r / 2
        match st.tuple j with
        | none => some (.compute ((p3Tuple n s).map fun tu =>
            { st with tuple := Function.update st.tuple j (some tu) }))
        | some tu =>
          match tu.find? (fun i => if h : i < n then !st.didSend r (.server ⟨i, h⟩) else false) with
          | some i =>
            if h : i < n then some (.send (.server ⟨i, h⟩) [true] (st.markSent r (.server ⟨i, h⟩)))
            else none
          | none => none
      else if 3 * T + 3 ≤ r ∧ r < 3 * T + 3 + K then
        let k := r - (3 * T + 3)
        match st.msgAt (3 * T + 2) .alice with
        | some (true :: _) =>
          match st.perm k with
          | none => some (.compute ((p3Perms 1 s).map fun ps =>
              { st with perm := Function.update st.perm k (some (ps.headD [])) }))
          | some ps =>
            if st.didSend r .alice then none
            else some (.send .alice (encList (Nat.size s) ps) (st.markSent r .alice))
        | _ => none
      else none
    | .alice =>
      let acc := p3Accepted s T w st
      if r = 3 * T + 2 then
        if st.didSend r .bob then none
        else if acc.length < K then some (.send .bob [false] (st.markSent r .bob))
        else
          let sel := acc.take K
          some (.send .bob
            (true :: ((List.range T).map fun j => decide (j ∈ sel)) ++
              encList w (sel.flatMap fun j => sortNat ((st.taggedAt w (2 * T + 1 + j)).map Prod.snd)))
            (st.markSent r .bob))
      else if 3 * T + 3 ≤ r ∧ r < 3 * T + 3 + K ∧ K ≤ acc.length then
        let k := r - (3 * T + 3)
        match st.perm k with
        | none => some (.compute ((p3Perms 1 s).map fun ps =>
            { st with perm := Function.update st.perm k (some (ps.headD [])) }))
        | some ps =>
          if st.didSend r .bob then none
          else some (.send .bob (encList (Nat.size s) ps) (st.markSent r .bob))
      else none
  recv _ r st fr m := { st with inbox := st.inbox ++ [(r, fr, m)] }
  outA st :=
    let s := s3 α
    let T := 32 * K
    let w := tagW s
    let acc := p3Accepted s T w st
    if K ≤ acc.length ∧ ∀ k < K,
        (st.perm k).isSome ∧ (st.msgAt (3 * T + 3 + k) .bob).isSome then
      let sel := acc.take K
      let U : Bool → Bits K := fun half k =>
        let j := sel.getD k.1 0
        let tb := st.taggedAt w (2 * T + 1 + j)
        let tags := sortNat (tb.map Prod.snd)
        let pa := (st.perm k.1).getD []
        let pb := decList (Nat.size s) s ((st.msgAt (3 * T + 3 + k.1) .bob).getD [])
        let bit : ℕ → Bool := fun tg => ((tb.find? fun x => decide (x.2 = tg)).map Prod.fst).getD false
        let σ : ℕ → ℕ := fun q => pb.getD (pa.getD q 0) 0
        xorList ((List.range s).filterMap fun q =>
          if decide (s / 2 ≤ σ q) = half then some (bit (tags.getD q 0)) else none)
      some (U false, U true)
    else none
  outB st :=
    let s := s3 α
    let T := 32 * K
    let w := tagW s
    match st.msgAt (3 * T + 2) .alice with
    | some (true :: rest) =>
      if ∀ k < K, (st.perm k).isSome ∧ (st.msgAt (3 * T + 3 + k) .alice).isSome then
        let selVec := rest.take T
        let sel := (List.range T).filter fun j => selVec.getD j false
        let tagsAll := decList w (K * s) (rest.drop T)
        let res : Fin K → Bool × Bool := fun k =>
          let j := sel.getD k.1 0
          let tags := (tagsAll.drop (k.1 * s)).take s
          let mine := st.taggedAt w (2 * j)
          let ru := tags.findIdx fun tg => !(mine.any fun x => decide (x.2 = tg))
          let pb := (st.perm k.1).getD []
          let pa := decList (Nat.size s) s ((st.msgAt (3 * T + 3 + k.1) .alice).getD [])
          let σ : ℕ → ℕ := fun q => pb.getD (pa.getD q 0) 0
          let C := decide (σ ru < s / 2)
          let bit : ℕ → Bool := fun tg => ((mine.find? fun x => decide (x.2 = tg)).map Prod.fst).getD false
          (C, xorList ((List.range s).filterMap fun q =>
            if q ≠ ru ∧ decide (s / 2 ≤ σ q) = C then some (bit (tags.getD q 0)) else none))
        some (fun k => (res k).1, fun k => (res k).2)
      else none
    | _ => none

/-! ### One trial's table (Section 7.3, Lemma 7.2) -/

/-- The raw randomness of one trial: every server's `(Z_i, L_i, volunteer)` and Bob's
request tuple (the same draws as in `protocol3`). -/
def p3TrialRaw (n s : ℕ) : PMF ((Fin n → Bool × ℕ × Bool) × List ℕ) :=
  (iidVec (p3Draw n s) n).bind fun dr => (p3Tuple n s).map fun tu => (dr, tu)

/-- Participants of a trial: requested or volunteered. -/
def p3Part {n : ℕ} (x : (Fin n → Bool × ℕ × Bool) × List ℕ) (i : Fin n) : Bool :=
  decide (i.1 ∈ x.2) || (x.1 i).2.2

/-- A trial is accepted: exactly `s` participants, with distinct tags. -/
def p3Accept {n : ℕ} (s : ℕ) (x : (Fin n → Bool × ℕ × Bool) × List ℕ) : Prop :=
  (Finset.univ.filter fun i => p3Part x i = true).card = s ∧
    ((Finset.univ.filter fun i => p3Part x i = true).image fun i => (x.1 i).2.1).card = s

/-- A table row: (status, volunteer flag, tag, bit).  Status `k ≥ 1`: the server is the
`k`-th entry of Bob's tuple; `0`: not requested. -/
abbrev Row := ℕ × Bool × ℕ × Bool

/-- The labeling of an accepted trial, as the map from table positions to server labels:
participants by increasing tag in positions `0, …, s-1`, then the nonparticipants in the
independent uniform order given by `ρ`. -/
def p3Labeling {n : ℕ} (x : (Fin n → Bool × ℕ × Bool) × List ℕ) (ρ : Equiv.Perm (Fin n)) :
    Fin n → Fin n :=
  let lp := ((List.finRange n).filter fun i => p3Part x i).mergeSort
    fun a b => decide ((x.1 a).2.1 ≤ (x.1 b).2.1)
  let ln := ((List.finRange n).filter fun i => !p3Part x i).mergeSort
    fun a b => decide (ρ a ≤ ρ b)
  fun pos => (lp ++ ln).getD pos.1 pos

/-- The table of a trial: row at position `pos` is the data of the server placed there. -/
def p3Table {n : ℕ} (x : (Fin n → Bool × ℕ × Bool) × List ℕ) (ρ : Equiv.Perm (Fin n)) :
    Fin n → Row :=
  fun pos =>
    let i := p3Labeling x ρ pos
    (if i.1 ∈ x.2 then x.2.idxOf i.1 + 1 else 0, (x.1 i).2.2, (x.1 i).2.1, (x.1 i).1)

/-- The accepted-trial distribution described in Lemma 7.2: sorted participant tags form a
uniform `s`-subset of the tag range; independently the unmatched position `T_tag` is uniform
on `{0, …, s-1}`; the other participant rows get statuses `1, …, s-1` by a uniform bijection;
the unmatched row has status `0` and volunteer flag `1`, nonparticipant rows status and flag
`0`, requested rows independent Bernoulli(`1/(n-s+1)`) flags; all `n` bits are independent
uniform and the nonparticipant tags independent uniform. -/
def p3AcceptedTableLaw (n s : ℕ) : PMF (Fin n → Row) :=
  if hs : 0 < s then
    haveI : NeZero s := ⟨hs.ne'⟩
    (unifSubsets (Finset.range (2 ^ tagW s)) s).bind fun S =>
      (PMF.uniformOfFintype (Fin s)).bind fun Tt =>
        (PMF.uniformOfFintype (Equiv.Perm (Fin (s - 1)))).bind fun π =>
          (iidVec (bern (1 / ((n : ℝ) - s + 1))) n).bind fun vols =>
            (iidVec unifBit n).bind fun bits =>
              (iidVec ((PMF.uniformOfFintype (Fin (2 ^ tagW s))).map Fin.val) n).map fun npt =>
                fun pos =>
                  let ts := S.sort (· ≤ ·)
                  if pos.1 < s then
                    if pos.1 = Tt.1 then (0, true, ts.getD pos.1 0, bits pos)
                    else
                      let idx := if pos.1 < Tt.1 then pos.1 else pos.1 - 1
                      (if h : idx < s - 1 then (π ⟨idx, h⟩).1 + 1 else 0, vols pos,
                        ts.getD pos.1 0, bits pos)
                  else (0, false, npt pos, bits pos)
  else PMF.pure fun _ => (0, false, 0, false)

end ChoiSemiHonestMPC.OTUpper


