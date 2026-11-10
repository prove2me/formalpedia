-- Prove2me | Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol2
-- name    : ChoiSemiHonestMPC_OTUpper_Protocol2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:31:22.51703+00:00
-- url     : https://prove2.me/theorems/5dfae56a-81db-409f-ba49-295c25d89f41
-- title:
--   Protocol 2 (Figure 6) with the parameters of Section 6.1
-- statement:
--   Protocol 1's $d,u,v,H$ are used for $K$ pairs on $|Q|=\lceil(1/2+\alpha)n\rceil$ servers at the effective fraction $2\alpha/(1+2\alpha)$. The caps use the original $n$: $\lceil 2nu/(1-v)\rceil$ for Alice and $\lceil 2nv/(1-u)\rceil$ for Bob. Round 0: Alice forms $A$, including each server independently with probability $u/(1-v)$, and Bob forms $B$ with probability $v/(1-u)$; each sends a one-bit status, failure when its set exceeds its cap. Round 1: if both succeeded, each sends REQUEST to its set. Round 2: each requested server replies to each requester with 1 iff the other client also requested it. Round 3: every server erases its entire state and stops. Each client derives $A\cap B$ from its own requests and replies, and lets $Q$ be the first $|Q|$ labels outside $A\cap B$ in the public order; it aborts if fewer remain. With $X_i=1[i\in A]$ and $Y_i=1[i\in B]$ on $Q$ (indexed $0,\dots,|Q|-1$), rounds 4–7 run Protocol 1's packing, record and output steps on $Q$. Any abort gives $\bot$.
-- source:
--   Choi 2026, STOC 2027 submission manuscript (sha256 3a47662a…), Sections 6.1–6.2 and Figure 6, p. 27–28 (PDF 29–30)

import Mathlib
import Definitions.Def_ChoiSemiHonestMPC_OTUpper_Protocol1

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ChoiSemiHonestMPC.OTUpper

/-! ### Protocol 2 parameters (Section 6.1) -/

/-- Number of retained servers `|Q| = ⌈(1/2 + α) n⌉`. -/
def qSize (α : ℝ) (n : ℕ) : ℕ := ⌈(1 / 2 + α) * n⌉₊

/-- Effective corruption fraction `2α / (1 + 2α)` used for Protocol 1's parameters. -/
def alphaEff (α : ℝ) : ℝ := 2 * α / (1 + 2 * α)

/-- Protocol 1's `d` at the effective fraction. -/
def d2 (α : ℝ) : ℕ := d1 (alphaEff α)

/-- Protocol 1's `u` for `K` pairs on `|Q|` servers at the effective fraction. -/
def u2 (α : ℝ) (n K : ℕ) : ℝ := u1 (alphaEff α) (qSize α n) K

/-- Protocol 1's `v` for `K` pairs on `|Q|` servers at the effective fraction. -/
def v2 (α : ℝ) (n K : ℕ) : ℝ := v1 (alphaEff α) (qSize α n) K

/-- Protocol 1's `H` for `K` pairs on `|Q|` servers at the effective fraction. -/
def H2 (α : ℝ) (n K : ℕ) : ℕ := H1 (alphaEff α) (qSize α n) K

/-- Alice's request cap `⌈2nu / (1 - v)⌉` (`n` the original number of servers). -/
def capA2 (α : ℝ) (n K : ℕ) : ℕ := ⌈2 * n * u2 α n K / (1 - v2 α n K)⌉₊

/-- Bob's request cap `⌈2nv / (1 - u)⌉`. -/
def capB2 (α : ℝ) (n K : ℕ) : ℕ := ⌈2 * n * v2 α n K / (1 - u2 α n K)⌉₊

/-- Both clients announced success in round 0: the other client's status message is
`[true]`, and the client's own request set is within its cap `cap`. -/
def statusOK {n : ℕ} (s : PState n) (cap : ℕ) (other : Party n) : Bool :=
  s.msgAt 0 other == some [true] &&
    (match s.req with
     | some R => decide (R.card ≤ cap)
     | none => false)

/-- The intersection `A ∩ B` as derived by a client from its own requests and the replies
of round 2 (`[true]` = collision). -/
def interFromReplies {n : ℕ} (s : PState n) : Finset ℕ :=
  ((s.inbox.filter fun e => decide (e.1 = 2) && e.2.2 == [true]).filterMap fun e =>
    match e.2.1 with
    | .server i => some i.1
    | _ => none).toFinset

/-- `Q`: the first `|Q|` server labels outside `A ∩ B` in the public order. -/
def qList (α : ℝ) (n : ℕ) (I : Finset ℕ) : List ℕ :=
  ((List.range n).filter fun i => decide (i ∉ I)).take (qSize α n)

/-- The positions `j < |Q|` of `Q` whose label lies in the request set `R`. -/
def onQ {n : ℕ} (Ql : List ℕ) (R : Finset (Fin n)) : Finset ℕ :=
  ((List.range Ql.length).filter fun j => decide (Ql.getD j 0 ∈ R.image Fin.val)).toFinset

/-- A Protocol 2 client may proceed after step 3: both announced success and enough labels
remain for `Q`. -/
def p2Ready (α : ℝ) {n : ℕ} (cap : ℕ) (other : Party n) (s : PState n) : Bool :=
  statusOK s cap other && decide ((qList α n (interFromReplies s)).length = qSize α n)

/-- **Protocol 2, general version (Figure 6)**.  Round 0: each client samples its request
set (each server independently, with probability `u/(1-v)` for Alice, `v/(1-u)` for Bob)
and sends a one-bit status (`[false]` = abort when its set exceeds its cap); round 1: if
both announced success, each client sends "REQUEST" (`[true]`) to every server of its set;
round 2: every requested server replies to each requester with `1` iff the other client
also requested it; round 3: every server erases its entire state and stops; rounds 4–7:
Protocol 1's packing, record and output steps on `Q` (positions `0, …, |Q|-1` in the public
order), with `X_i = 1[i ∈ A]`, `Y_i = 1[i ∈ B]`.  Any abort gives `⊥`. -/
def protocol2 (α : ℝ) (n K : ℕ) :
    Protocol n Unit Unit (Bits K × Bits K) (Bits K × Bits K) where
  S := PState n
  initA _ := {}
  initB _ := {}
  initS _ := {}
  rounds := 8
  opBound := 2 * n + 8
  act p r s :=
    let m := qSize α n
    let d := d2 α
    let H := H2 α n K
    let reqStep (prob : ℝ) (cap : ℕ) (other : Party n) : Option (Op n (PState n)) :=
      if r = 0 then
        match s.req with
        | none => some (.compute ((iidVec (bern prob) n).map fun v =>
            { s with req := some (Finset.univ.filter fun i => v i = true) }))
        | some R =>
          if s.didSend 0 other then none
          else some (.send other [decide (R.card ≤ cap)] (s.markSent 0 other))
      else if r = 1 then
        match s.req with
        | some R =>
          if s.msgAt 0 other == some [true] && decide (R.card ≤ cap) then
            match (R.sort (· ≤ ·)).find? (fun i => !s.didSend 1 (.server i)) with
            | some i => some (.send (.server i) [true] (s.markSent 1 (.server i)))
            | none => none
          else none
        | none => none
      else none
    match p with
    | .alice =>
      if r < 4 then reqStep (u2 α n K / (1 - v2 α n K)) (capA2 α n K) .bob
      else if p2Ready α (capA2 α n K) .bob s then
        let Ql := qList α n (interFromReplies s)
        packAct m d H K 4 .alice (onQ Ql (s.req.getD ∅)) ∅ r s
      else none
    | .bob =>
      if r < 4 then reqStep (v2 α n K / (1 - u2 α n K)) (capB2 α n K) .alice
      else if p2Ready α (capB2 α n K) .alice s then
        let Ql := qList α n (interFromReplies s)
        packAct m d H K 4 .bob ∅ (onQ Ql (s.req.getD ∅)) r s
      else none
    | .server _ =>
      if r = 2 then
        let reqA := (s.msgAt 1 .alice).isSome
        let reqB := (s.msgAt 1 .bob).isSome
        if reqA && !s.didSend 2 .alice then
          some (.send .alice [reqA && reqB] (s.markSent 2 .alice))
        else if reqB && !s.didSend 2 .bob then
          some (.send .bob [reqA && reqB] (s.markSent 2 .bob))
        else none
      else if r = 3 ∧ !s.erased then some (.compute (PMF.pure { erased := true }))
      else none
  recv _ r s fr m := storeMsg r s fr m
  outA s :=
    if p2Ready α (capA2 α n K) .bob s then
      packOutA (d2 α) (H2 α n K) K 4 (onQ (qList α n (interFromReplies s)) (s.req.getD ∅)) s
    else none
  outB s :=
    if p2Ready α (capB2 α n K) .alice s then
      packOutB (qSize α n) (d2 α) (H2 α n K) K 4
        (onQ (qList α n (interFromReplies s)) (s.req.getD ∅)) s
    else none

end ChoiSemiHonestMPC.OTUpper


