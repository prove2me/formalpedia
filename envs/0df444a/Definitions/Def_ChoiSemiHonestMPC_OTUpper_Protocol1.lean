-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol1
-- name    : ChoiSemiHonestMPC_OTUpper_Protocol1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:29:57.851196+00:00
-- url     : https://prove2.me/theorems/63a7a286-266d-46b5-a478-95a2ddc61bac
-- title:
--   Protocol 1 (Figure 5) with the parameters of Section 5.1
-- statement:
--   Parameters: $d=\lceil 4/(1-2\alpha)^2\rceil$, $c_\alpha=(1-2\alpha)^2/(12288(2d-1)^2)$, $u=(2d-1)\sqrt{12K/(n\log_2 n)}$, $v=u\log_2 n$, $H=\lceil 2(2d-1)K(1-u)/v\rceil$. A packing for the notification set $X$ is an ordered list of $H$ blocks of $2d$ labels, with no repeated label, each block containing exactly one label outside $X$ (its hole). There are $Z=(k)_{(2d-1)H}(m-k)_H(2d)^H$ packings, where $k=|X|$; `packEnum` is a fixed deterministic enumeration of them. A selection is an ordered collection of $K$ records of $2d$ blocks each, with no repeated block index and exactly one unknown block per record. In round 0 each server draws ALICE, BOB or SLEEP with probabilities $(u,v,1-u-v)$ and sends the one-bit HELLO to Alice, to Bob, or to nobody. After its delivery, a server can separately erase immediately in round 0; round 1 is the completion barrier. Round 2: Alice sends $\sum X_i$ and samples $A$; she sends an abort announcement and aborts if $\sum X_i<(2d-1)H$ or $n-\sum X_i<H$. Round 3: Bob samples $B$ and sends it. Round 4: Alice sends the packing with index $(A+B)\bmod Z$. Round 5: Bob announces abort if there are fewer than $(2d-1)K$ known or fewer than $K$ unknown blocks; otherwise he samples a selection uniformly using only the known/unknown pattern and sends it. Outputs, with positions counted from 0: Alice $U_b=\bigoplus_{j:\lfloor j/d\rfloor=b}1[J_j\ge d]$. Bob $C=1$ iff the unknown block lies in the first half, i.e. $C=1-\lfloor T/d\rfloor$, and $U_C$ from the holes of the known blocks of half $C$, which he knows. Any abort gives $\bot$. The packing, record and output steps (`packAct`, `packOutA`, `packOutB`) are stated for a general pool of $m$ positions, so Protocol 2 can reuse them.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Section 5.1 and Figure 5, p. 20–22 (PDF 22–24)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Security

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-! ### Encodings of messages as bit strings -/

/-- `k` written with exactly `w` bits (least significant first). -/
def encNat (w k : ℕ) : Msg := (List.range w).map fun j => k.testBit j

/-- Inverse of `encNat` (for `k < 2 ^ w`). -/
def decNat (l : Msg) : ℕ := l.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0

/-- A list of numbers, each written with `w` bits. -/
def encList (w : ℕ) (l : List ℕ) : Msg := (l.map (encNat w)).flatten

/-- The first `cnt` numbers of width `w` of a message. -/
def decList (w cnt : ℕ) (l : Msg) : List ℕ :=
  (List.range cnt).map fun j => decNat ((l.drop (j * w)).take w)

/-- XOR of a list of bits. -/
def xorList (l : List Bool) : Bool := l.foldl xor false

/-! ### Party state shared by Protocols 1 and 2 -/

/-- Private state of a party in Protocols 1 and 2 (fields unused by a party stay at their
defaults).  `w`: a server's sampled action (`0` = ALICE, `1` = BOB, `2` = SLEEP);
`erased`: the server has erased its entire state and stopped; `sentTo`: the sends already
made, by round and recipient; `inbox`: received messages with their round and sender;
`share`: a client's packing-index share (`A` or `B`); `pack`: the packing Alice sent
(flattened server labels); `recs`: the records Bob selected (flattened block indices);
`req`: a Protocol 2 client's request set. -/
structure PState (n : ℕ) where
  w : Option (Fin 3) := none
  erased : Bool := false
  sentTo : List (ℕ × Party n) := []
  inbox : List (ℕ × Party n × Msg) := []
  share : Option ℕ := none
  pack : Option (List ℕ) := none
  recs : Option (List ℕ) := none
  req : Option (Finset (Fin n)) := none
  packingAbortAnnounced : Bool := false

/-- The message received from `q` in round `r`, if any. -/
def PState.msgAt {n : ℕ} (s : PState n) (r : ℕ) (q : Party n) : Option Msg :=
  (s.inbox.find? fun e => decide (e.1 = r ∧ e.2.1 = q)).map fun e => e.2.2

/-- Labels of the servers whose message arrived in round `r`. -/
def PState.serversAt {n : ℕ} (s : PState n) (r : ℕ) : Finset ℕ :=
  ((s.inbox.filter fun e => decide (e.1 = r)).filterMap fun e =>
    match e.2.1 with
    | .server i => some i.1
    | _ => none).toFinset

/-- Has the party already sent to `q` in round `r`? -/
def PState.didSend {n : ℕ} (s : PState n) (r : ℕ) (q : Party n) : Bool :=
  decide ((r, q) ∈ s.sentTo)

/-- Record a send. -/
def PState.markSent {n : ℕ} (s : PState n) (r : ℕ) (q : Party n) : PState n :=
  { s with sentTo := s.sentTo ++ [(r, q)] }

/-! ### Protocol 1 parameters (Section 5.1) -/

/-- `d = ⌈4 / (1 - 2α)^2⌉` (block length `2d`). -/
def d1 (α : ℝ) : ℕ := ⌈4 / (1 - 2 * α) ^ 2⌉₊

/-- `c_α = (1 - 2α)^2 / (12288 (2d - 1)^2)`. -/
def cAlpha1 (α : ℝ) : ℝ := (1 - 2 * α) ^ 2 / (12288 * (2 * (d1 α : ℝ) - 1) ^ 2)

/-- `u = (2d - 1) √(12K / (n log₂ n))`: probability that a server notifies Alice. -/
def u1 (α : ℝ) (n K : ℕ) : ℝ :=
  (2 * (d1 α : ℝ) - 1) * Real.sqrt (12 * K / (n * Real.logb 2 n))

/-- `v = u log₂ n`: probability that a server notifies Bob. -/
def v1 (α : ℝ) (n K : ℕ) : ℝ := u1 α n K * Real.logb 2 n

/-- `H = ⌈2 (2d - 1) K (1 - u) / v⌉`: number of blocks in the packing. -/
def H1 (α : ℝ) (n K : ℕ) : ℕ :=
  ⌈2 * (2 * (d1 α : ℝ) - 1) * K * (1 - u1 α n K) / v1 α n K⌉₊

/-! ### Packings and records on a pool of `m` servers (labels `0, …, m-1`) -/

/-- An ordered list of `H` blocks, each an ordered list of `2d` server labels. -/
abbrev Packing (m d H : ℕ) := Fin H → Fin (2 * d) → Fin m

/-- A packing for the notification set `X`: no label repeats, and every block contains
exactly one label outside `X` (its hole). -/
def IsPacking {m d H : ℕ} (X : Finset (Fin m)) (G : Packing m d H) : Prop :=
  Function.Injective (fun x : Fin H × Fin (2 * d) => G x.1 x.2) ∧
    ∀ k, (Finset.univ.filter fun j => G k j ∉ X).card = 1

/-- The number of packings when `k` servers notified Alice:
`Z = (k)_{(2d-1)H} (m-k)_H (2d)^H` (falling factorials). -/
def packZ (m d H k : ℕ) : ℕ :=
  k.descFactorial ((2 * d - 1) * H) * (m - k).descFactorial H * (2 * d) ^ H

/-- Flatten a packing to its list of labels, block by block. -/
def packFlat {m d H : ℕ} (G : Packing m d H) : List ℕ :=
  (List.finRange H).flatMap fun k => (List.finRange (2 * d)).map fun j => (G k j).1

open Classical in
/-- The fixed deterministic enumeration of the packings of a notification set: index `i`
is mapped to the `i`-th packing in a fixed enumeration of that (finite) set. -/
def packEnum (m d H : ℕ) (X : Finset ℕ) (i : ℕ) : Option (List ℕ) :=
  let Xf : Finset (Fin m) := Finset.univ.filter fun j => j.1 ∈ X
  if h : i < Fintype.card {G : Packing m d H // IsPacking Xf G} then
    some (packFlat ((Fintype.equivFin {G : Packing m d H // IsPacking Xf G}).symm ⟨i, h⟩).1)
  else none

/-- Block `k` of a flattened packing. -/
def blockOf (d : ℕ) (G : List ℕ) (k : ℕ) : List ℕ := (G.drop (k * (2 * d))).take (2 * d)

/-- Is block `k` known to Bob (one of its servers notified him)? -/
def knownBlock (d : ℕ) (Y : Finset ℕ) (G : List ℕ) (k : ℕ) : Bool :=
  (blockOf d G k).any fun x => decide (x ∈ Y)

/-- An ordered collection of `K` records: record `k` is an ordered list of `2d` block
indices. -/
abbrev Selection (K d H : ℕ) := Fin K → Fin (2 * d) → Fin H

/-- `K` disjoint records (no block index repeats), each containing exactly one block
unknown to Bob. -/
def IsSelection {K d H : ℕ} (known : Fin H → Bool) (R : Selection K d H) : Prop :=
  Function.Injective (fun x : Fin K × Fin (2 * d) => R x.1 x.2) ∧
    ∀ k, (Finset.univ.filter fun j => known (R k j) = false).card = 1

/-- Flatten a selection. -/
def selFlat {K d H : ℕ} (R : Selection K d H) : List ℕ :=
  (List.finRange K).flatMap fun k => (List.finRange (2 * d)).map fun j => (R k j).1

open Classical in
/-- Bob's uniform choice of an ordered collection of `K` disjoint records, using only the
known/unknown pattern of the blocks and fresh coins (`none` if there is none). -/
def selectRecords (K d H : ℕ) (known : Fin H → Bool) : Option (PMF (List ℕ)) :=
  if h : (Finset.univ.filter fun R : Selection K d H => IsSelection known R).Nonempty then
    some ((PMF.uniformOfFinset _ h).map selFlat)
  else none

/-! ### The packing, record and output steps (Figure 5, steps 2–4) on a pool -/

/-- Alice aborts in step 2 when fewer than `(2d-1)H` or more than `m - H` servers of the
pool notified her. -/
def packAbort (m d H k : ℕ) : Bool := decide (k < (2 * d - 1) * H ∨ m - k < H)

/-- Steps 2–3 for the clients on a pool of `m` servers, starting at round `r0`.  `X` is
the set of pool positions that notified Alice (used by Alice), `Y` those that notified Bob
(used by Bob).  Round `r0`: Alice sends `∑ X_i` and samples `A`; round `r0+1`: Bob samples
and sends `B`; round `r0+2`: Alice sends the packing with index `(A + B) mod Z`; round
`r0+3`: Bob announces abort (`[false]`) or samples and sends the records. -/
def packAct {n : ℕ} (m d H K r0 : ℕ) (p : Party n) (X Y : Finset ℕ) (r : ℕ) (s : PState n) :
    Option (Op n (PState n)) :=
  match p with
  | .alice =>
    let k := X.card
    let Z := packZ m d H k
    if r = r0 then
      if !s.didSend r0 .bob then
        some (.send .bob (encNat (Nat.size m) k) (s.markSent r0 .bob))
      else if packAbort m d H k && !s.packingAbortAnnounced then
        some (.send .bob [false] { s with packingAbortAnnounced := true })
      else if !packAbort m d H k && s.share.isNone then
        if h : 0 < Z then
          haveI : NeZero Z := ⟨h.ne'⟩
          some (.compute ((PMF.uniformOfFintype (Fin Z)).map fun a => { s with share := some a.1 }))
        else none
      else none
    else if r = r0 + 2 then
      match s.share, s.msgAt (r0 + 1) .bob, s.didSend (r0 + 2) .bob with
      | some a, some bm, false =>
        match packEnum m d H X ((a + decNat bm) % Z) with
        | some g => some (.send .bob (encList (Nat.size m) g)
            { (s.markSent (r0 + 2) .bob) with pack := some g })
        | none => none
      | _, _, _ => none
    else none
  | .bob =>
    if r = r0 + 1 then
      match s.msgAt r0 .alice with
      | some km =>
        let k := decNat km
        let Z := packZ m d H k
        if packAbort m d H k then none
        else
          match s.share with
          | none =>
            if h : 0 < Z then
              haveI : NeZero Z := ⟨h.ne'⟩
              some (.compute ((PMF.uniformOfFintype (Fin Z)).map fun b => { s with share := some b.1 }))
            else none
          | some b =>
            if s.didSend (r0 + 1) .alice then none
            else some (.send .alice (encNat (Nat.size Z) b) (s.markSent (r0 + 1) .alice))
      | none => none
    else if r = r0 + 3 then
      match s.msgAt (r0 + 2) .alice with
      | some gm =>
        let G := decList (Nat.size m) (H * (2 * d)) gm
        let known : Fin H → Bool := fun k => knownBlock d Y G k.1
        let nKnown := (Finset.univ.filter fun k => known k = true).card
        if s.didSend (r0 + 3) .alice then none
        else if nKnown < (2 * d - 1) * K ∨ H - nKnown < K then
          some (.send .alice [false] (s.markSent (r0 + 3) .alice))
        else
          match s.recs with
          | some R => some (.send .alice (true :: encList (Nat.size H) R)
              (s.markSent (r0 + 3) .alice))
          | none =>
            match selectRecords K d H known with
            | some μ => some (.compute (μ.map fun R => { s with recs := some R }))
            | none => none
      | none => none
    else none
  | .server _ => none

/-- Step 4 for Alice: for record `k` with holes `J_1, …, J_{2d}` (positions counted from
`0` here), `U_b = ⊕_{j : ⌊j/d⌋ = b} 1[J_j ≥ d]` (the paper's `1[J_k > d]` with positions
counted from `1`). -/
def packOutA {n : ℕ} (d H K r0 : ℕ) (X : Finset ℕ) (s : PState n) : Option (Bits K × Bits K) :=
  match s.msgAt (r0 + 3) .bob, s.pack with
  | some (true :: rm), some G =>
    let R := decList (Nat.size H) (K * (2 * d)) rm
    let hole : ℕ → ℕ := fun blk => (blockOf d G blk).findIdx fun x => decide (x ∉ X)
    let U : Bool → Bits K := fun b k =>
      xorList ((List.range (2 * d)).filterMap fun j =>
        if decide (d ≤ j) = b then some (decide (d ≤ hole (R.getD (k.1 * (2 * d) + j) 0)))
        else none)
    some (U false, U true)
  | _, _ => none

/-- Step 4 for Bob: `T` is the position of the unknown block, `C = 1 - ⌊T/d⌋` (positions
from `0`; the paper's `1 - ⌊(T-1)/d⌋`), i.e. `C` names the half not containing the unknown
block; `U_C` is computed from the known blocks of half `C`, whose holes Bob knows (the
position of the server that notified him). -/
def packOutB {n : ℕ} (m d H K r0 : ℕ) (Y : Finset ℕ) (s : PState n) :
    Option (Bits K × Bits K) :=
  match s.recs, s.msgAt (r0 + 2) .alice with
  | some R, some gm =>
    let G := decList (Nat.size m) (H * (2 * d)) gm
    let blk : ℕ → ℕ → ℕ := fun k j => R.getD (k * (2 * d) + j) 0
    let T : ℕ → ℕ := fun k => (List.range (2 * d)).findIdx fun j => !knownBlock d Y G (blk k j)
    let C : Bits K := fun k => decide (T k.1 < d)
    let holeB : ℕ → ℕ := fun b => (blockOf d G b).findIdx fun x => decide (x ∈ Y)
    let UC : Bits K := fun k =>
      xorList ((List.range (2 * d)).filterMap fun j =>
        if decide (d ≤ j) = C k then some (decide (d ≤ holeB (blk k.1 j))) else none)
    some (C, UC)
  | _, _ => none

/-- A server's action in step 1: ALICE (`0`) with probability `u`, BOB (`1`) with
probability `v`, SLEEP (`2`) otherwise. -/
def triAction (u v : ℝ) : PMF (Fin 3) :=
  (bern u).bind fun a =>
    if a then PMF.pure 0 else (bern (v / (1 - u))).map fun b => if b then 1 else 2

/-- Clients store every received message with its round and sender. -/
def storeMsg {n : ℕ} (r : ℕ) (s : PState n) (fr : Party n) (m : Msg) : PState n :=
  { s with inbox := s.inbox ++ [(r, fr, m)] }

/-- **Protocol 1, general version (Figure 5)**, generating `K` wROT pairs with `n`
servers at corruption fraction `α`. Round 0: each server samples its action and sends
"HELLO" (the one-bit message `[true]`) to Alice or Bob, or nothing, then separately erases
after delivery. Round 1 is an erasure-completion barrier; rounds 2–5: packing and record selection on
the pool of all `n` servers with `X` = servers that notified Alice, `Y` = servers that
notified Bob; outputs `(U0, U1)` for Alice and `(C, U_C)` for Bob, `⊥` on abort. -/
def protocol1 (α : ℝ) (n K : ℕ) :
    Protocol n Unit Unit (Bits K × Bits K) (Bits K × Bits K) where
  S := PState n
  initA _ := {}
  initB _ := {}
  initS _ := {}
  rounds := 6
  opBound := 2 * n + 8
  act p r s :=
    match p with
    | .server _ =>
      if s.erased then none
      else if r = 0 then
        match s.w with
        | none => some (.compute ((triAction (u1 α n K) (v1 α n K)).map fun a => { s with w := some a }))
        | some a =>
          if a = 0 ∧ !s.didSend 0 .alice then some (.send .alice [true] (s.markSent 0 .alice))
          else if a = 1 ∧ !s.didSend 0 .bob then some (.send .bob [true] (s.markSent 0 .bob))
          else some (.erase { erased := true })
      else if r = 1 ∧ !s.erased then some (.erase { erased := true })
      else none
    | _ => packAct n (d1 α) (H1 α n K) K 2 p (s.serversAt 0) (s.serversAt 0) r s
  recv _ r s fr m := storeMsg r s fr m
  outA s := packOutA (d1 α) (H1 α n K) K 2 (s.serversAt 0) s
  outB s := packOutB n (d1 α) (H1 α n K) K 2 (s.serversAt 0) s

end ChoiSemiHonestMPC.OTUpper


