-- Prove2me | Definitions.Def_ShiAuthentication_BA_Protocols
-- name    : ShiAuthentication_BA_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:10:11.358951+00:00
-- url     : https://prove2.me/theorems/848ff2df-2bc6-492a-8bed-a27441777733
-- title:
--   Protocols 1–3: $\Pi_{\mathrm{Confirm}}$, $\Pi_{\mathrm{GBA}}$ and the phase-king protocol $\Pi_{\mathrm{BA}}$
-- statement:
--   The three protocols of §4.2, written as deterministic protocols of the execution model. They use only each party's own initial data: $n$, $t$, its name, its key and its local key table. Every signed payload carries the identifier of its call (protocol, phase, index of the call in the phase), the message type, the signer, and $G$ when $G$ is public.
--
--   1. **$\Pi_{\mathrm{Confirm}}$ (Protocol 1, two rounds).** Each party $p$ has an input bit $b_p$. Round 1: each $x$ sends everyone $(x,vk_x,b_x,\sigma_x)$ with $\sigma_x$ a signature on the payload under its key. Party $p$ records $m_{x,p}$ if the message has this format, signer field $x$, a bit in $\{0,1\}$ and a valid signature, and $\bot$ otherwise; $m_{p,p}$ is its own message; $\widehat{vk}_{x,p}$ is the key in a valid record. Round 2: each $j$ sends everyone its whole vector $(m_{x,j})_x$ and its key table. Invalid second-round messages and records whose signer does not match the vector position are ignored. Then $x\in\mathrm{Supp}_p$ iff $m_{x,p}$ carries $b_p$ and no second-round vector (including $p$'s own) contains a valid message from $x$ on $1-b_p$ under $\widehat{vk}_{x,p}$. The conflict graph $\Gamma_p$ on $\mathrm{Supp}_p$ has the edge $\{x,j\}$ ($x\neq j$) when a table entry $(x,\widehat{vk})$ received from $j$ (or in $p$'s own table) has $\widehat{vk}\neq\widehat{vk}_{x,p}$. With $\nu$ the maximum matching size, $p$ outputs
--   $$\begin{cases} b_p & \text{if } |\mathrm{Supp}_p|-\nu(\Gamma_p)\ge n-t,\\ \bot & \text{otherwise.}\end{cases}$$
--   2. **$\Pi_{\mathrm{GBA}}$ (Protocol 2, four rounds).** Start with $c_p=x_p$, $g_p=0$. Call $\Pi_{\mathrm{Confirm}}$ on $c_p$; if it returns $0$ set $g_p=1$; replace $\bot$ by $0$. Call $\Pi_{\mathrm{Confirm}}$ again on the new $c_p$; if it returns $1$ set $g_p=1$; replace $\bot$ by $1$. Output $(c_p,g_p)$. Both calls are always executed and the grade is never reset.
--   3. **$\Pi_{\mathrm{BA}}$ (Protocol 3, $5(t+1)$ rounds).** The kings are the parties $0,1,\dots,t$ in this order. Starting from $x_p=b_p$, phase $j$ runs $\Pi_{\mathrm{GBA}}$ on the current bits (four rounds) and then a king round in which king $j$ sends its candidate bit to everyone; a party with grade $1$ sets $x_p=c_p$, any other party takes the king's bit ($0$ if the message is missing or invalid), and the king uses its own candidate. After $t+1$ phases each party outputs $x_p$.
--
--   These are the protocols whose correctness and costs Lemmas 4.4–4.5 and Theorem 4.6 assert.
--
--   **Formalization Note** Bits are the numbers $0,1$. Edges of $\Gamma_p$ are pairs $(\min,\max)$ of names; $\nu$ is defined as the largest size of a pairwise vertex-disjoint edge subset (a semantic value; how it is computed is a separate matter for the cost claim). The output test is written $n+\nu\le|\mathrm{Supp}_p|+t$, which is the same comparison without truncated subtraction. Standalone $\Pi_{\mathrm{Confirm}}$ and $\Pi_{\mathrm{GBA}}$ read their input from the party's input bit and use the fixed call identifiers $(0,0,\cdot)$ and $(1,0,\cdot)$; $\Pi_{\mathrm{BA}}$ uses $(2,j,\cdot)$ in phase $j$.
--
--   **Invocation and wire-format convention (moderation repair).** The call context additionally includes the fresh root session and designated sender. `directLimit` and `forwardLimit` fix concrete O(κ) and O(nκ) packet formats using the actual `encMsg` bit length. Oversized packets are invalid; faulty parties may still send arbitrary terms. A bounded prefix plus an overflow bit suffices to reject such packets before vector/table decoding. The constants 256 and 64 specify this codec's format envelope, not a claimed value of the paper's communication constant. No honest packet on a compatible setup is rejected. Each honest forwarded vector contains bounded valid direct records, including its own locally constructed record. General conflict graphs remain unrestricted, and matching is a semantic maximum, with polynomial implementation asserted separately as a theorem conclusion.
-- source:
--   Kecheng Shi, STOC 2027 submission #203 (October 2026), Protocol 1 (Π_Confirm) p. 19, Protocol 2 (Π_GBA) p. 20, Protocol 3 (Π_BA) p. 21; signed-data convention §3.1 p. 15

import Definitions.Def_ShiAuthentication_BA_Execution

set_option autoImplicit false

namespace ShiAuthentication.BA

/-! # Protocols 1–3: `Π_Confirm`, `Π_GBA` and `Π_BA`

Shi, STOC 2027 submission #203, §4.2: Protocol 1 (p. 19), Protocol 2 (p. 20), Protocol 3
(p. 21). All three use only the party's own initial data (`n`, `t`, its name, its own key and its
local key table); `G` appears only inside signed data when the public-graph setting supplies it
("the signed data include … G if G is public", p. 15). Parties are named `0, …, n−1`. Bit `b` is
the number `bitNum b ∈ {0, 1}`. -/

/-- A list as a nested tuple. -/
def listMsg (l : List Msg) : Msg := l.foldr Msg.cons Msg.nil

/-- A list of expressions as a nested tuple expression. -/
def listExpr (l : List Expr) : Expr := l.foldr Expr.cons Expr.nil

/-- A signature-free message written as an expression (signature atoms cannot be written and
become `nil`; only applied to signature-free terms below). -/
def Expr.ofPlain : Msg → Expr
  | .num k => .num k
  | .key k => .key k
  | .sig _ _ => .nil
  | .nil => .nil
  | .cons a b => .cons (Expr.ofPlain a) (Expr.ofPlain b)

/-- Read a nested tuple ending in `nil` as a list. -/
def Msg.toList? : Msg → Option (List Msg)
  | .nil => some []
  | .cons a b => (Msg.toList? b).map (a :: ·)
  | _ => none

/-- The number encoding a bit. -/
def bitNum (b : Bool) : ℕ := if b then 1 else 0

/-- `G` as signed data in the public-graph setting; `nil` in the local-table setting. -/
def graphMsg : Option (List (ℕ × ℕ)) → Msg
  | none => .nil
  | some es => .cons (.num 1) (listMsg (es.map fun e => .cons (.num e.1) (.num e.2)))

/-- The identifier of one call of `Π_Confirm`: protocol tag (`0` standalone `Π_Confirm`, `1`
standalone `Π_GBA`, `2` `Π_BA`), fresh root session, designated sender, phase, index of the call inside the phase, and `G` if public.
Distinct calls of one execution have distinct identifiers. -/
def callCtx (I : LocalInit) (proto phase call : ℕ) : Msg :=
  listMsg [.num I.session, .num proto,
    (match I.sender with | none => .nil | some x => .cons (.num x) .nil),
    .num phase, .num call, graphMsg I.graph]

/-- Maximum direct-record wire length. The fixed coefficient bounds this concrete codec's
format overhead, not the theorem's O(·) constant. Public graph data are included when present. -/
def directLimit (I : LocalInit) : ℕ :=
  256 * (I.κ + 1) + 4 * (encMsg (graphMsg I.graph)).length

/-- Maximum second-round packet length: one bounded direct record per signer and a table.
Reading one extra bit detects overflow; the rest of an oversized packet is discarded. -/
def forwardLimit (I : LocalInit) : ℕ :=
  (I.n + 1) * (directLimit I + 64 * (I.κ + 1))

/-- The signed data of a first-round message of `Π_Confirm`: call identifier, message type
(`0` = direct), signer `x`, its key `k` and bit `b`. -/
def payload (ctx : Msg) (x k : ℕ) (b : Bool) : Msg :=
  listMsg [ctx, .num 0, .num x, .key k, .num (bitNum b)]

/-- The first-round message `(x, vk_x, b_x, σ_x)` of `Π_Confirm`. -/
def directMsg (ctx : Msg) (x k : ℕ) (b : Bool) : Msg :=
  listMsg [.num x, .key k, .num (bitNum b), .sig k (payload ctx x k b)]

/-- The honest sender's expression for `directMsg`, signing with its own capability. -/
def directExpr (ctx : Msg) (x k : ℕ) (b : Bool) : Expr :=
  listExpr [.num x, .key k, .num (bitNum b), .signOwn (Expr.ofPlain (payload ctx x k b))]

/-- Protocol 1, round 1 record: a message counts as a valid direct message of signer `x` if it
has the prescribed format, its signer field is `x`, its bit is in `{0,1}` and its signature
verifies under the key it contains. Returns that key `vk̂` and the bit; otherwise `⊥` (`none`). -/
def parseDirectRaw (ctx : Msg) (x : ℕ) : Msg → Option (ℕ × Bool)
  | .cons (.num x') (.cons (.key k) (.cons (.num b) (.cons σ .nil))) =>
      if x' = x ∧ b ≤ 1 ∧ verify k (payload ctx x k (decide (b = 1))) σ = true then
        some (k, decide (b = 1))
      else none
  | _ => none

/-- Bounded direct-record parser. Length is with respect to the actual wire encoding;
this predicate can be checked from at most `limit + 1` received bits. -/
def parseDirect (limit : ℕ) (ctx : Msg) (x : ℕ) (m : Msg) : Option (ℕ × Bool) :=
  if (encMsg m).length ≤ limit then parseDirectRaw ctx x m else none

/-- A table entry `(x, vk̂)` of a forwarded key table. -/
def parseEntry : Msg → Option (ℕ × ℕ)
  | .cons (.num x) (.key k) => some (x, k)
  | _ => none

/-- Protocol 1, round 2 message from `j`: a vector with exactly one position per signer
`x = 0, …, n−1` and a key table with at most one entry per `x ≠ j`, `x < n`. An invalid message is
ignored (`none`). Inside a valid vector, a position holding anything but a valid direct message
of the signer of that position is ignored (`none`). -/
def parseForwardRaw (limit : ℕ) (ctx : Msg) (n j : ℕ) (m : Msg) :
    Option (List (Option (ℕ × Bool)) × List (ℕ × ℕ)) :=
  match m with
  | .cons vec tab =>
      match Msg.toList? vec, Msg.toList? tab with
      | some vs, some ts =>
          let es := ts.map parseEntry
          let tbl := es.filterMap id
          if vs.length = n ∧ es.all Option.isSome = true ∧
              tbl.all (fun e => decide (e.1 < n ∧ e.1 ≠ j)) = true ∧ (tbl.map Prod.fst).Nodup then
            some ((List.range n).map (fun x => parseDirect limit ctx x (vs.getD x .nil)), tbl)
          else none
      | _, _ => none
  | _ => none

/-- Reject an oversized round-two packet before decoding its vector/table. Within a
bounded packet, malformed forwarded records are independently ignored by `parseDirect`. -/
def parseForward (I : LocalInit) (ctx : Msg) (j : ℕ) (m : Msg) :
    Option (List (Option (ℕ × Bool)) × List (ℕ × ℕ)) :=
  if (encMsg m).length ≤ forwardLimit I then parseForwardRaw (directLimit I) ctx I.n j m
  else none

/-- Party `I.self`'s first-round record `m_{x,p}` of signer `x` as (key `vk̂_{x,p}`, bit); its own
record is its own message. -/
def directRec (I : LocalInit) (ctx : Msg) (b : Bool) (rcv0 : List (Option Msg)) (x : ℕ) :
    Option (ℕ × Bool) :=
  if x = I.self then some (I.ownKey, b)
  else match rcv0.getD x none with
    | some m => parseDirect (directLimit I) ctx x m
    | none => none

/-- `ν`: the maximum size of a matching in an undirected graph given by its edges `(a, b)`. -/
def IsMatchingSet (M : Finset (ℕ × ℕ)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' → e.1 ≠ e'.1 ∧ e.1 ≠ e'.2 ∧ e.2 ≠ e'.1 ∧ e.2 ≠ e'.2

instance (M : Finset (ℕ × ℕ)) : Decidable (IsMatchingSet M) := by
  unfold IsMatchingSet; infer_instance

/-- Maximum matching size `ν` of the edge set `E`. (A semantic value; how it is computed is a
matter for the local-computation bound, not for this definition.) -/
def maxMatching (E : Finset (ℕ × ℕ)) : ℕ :=
  ((E.powerset).filter IsMatchingSet).sup Finset.card

/-- `Supp_p` (Protocol 1, step 1): signers `x` whose direct record carries `p`'s bit `b`, such that
no second-round vector — `p`'s own vector or a valid forwarded one — contains a valid message
from `x` on `1 − b` under the same key `vk̂_{x,p}`. -/
def confirmSupp (I : LocalInit) (ctx : Msg) (b : Bool) (rcv0 rcv1 : List (Option Msg)) :
    Finset ℕ :=
  let own := (List.range I.n).map (directRec I ctx b rcv0)
  let fwd := (List.range I.n).filterMap fun j =>
    if j = I.self then none
    else match rcv1.getD j none with
      | some m => (parseForward I ctx j m).map Prod.fst
      | none => none
  (Finset.range I.n).filter fun x =>
    (match directRec I ctx b rcv0 x with
      | some (k, b') => decide (b' = b) && (own :: fwd).all (fun vec => vec.getD x none ≠ some (k, !b))
      | none => false) = true

/-- The conflict graph `Γ_p` on `Supp_p` (Protocol 1, step 1): for each table entry `(x, vk̂)`
received from `j` (or in `p`'s own table, `j = p`), with distinct `x, j ∈ Supp_p`, the edge
`{x, j}` if `vk̂ ≠ vk̂_{x,p}`. Edges are stored as `(min, max)`. -/
def confirmConflicts (I : LocalInit) (ctx : Msg) (b : Bool) (rcv0 rcv1 : List (Option Msg)) :
    Finset (ℕ × ℕ) :=
  let S := confirmSupp I ctx b rcv0 rcv1
  let tables : List (ℕ × List (ℕ × ℕ)) := (I.self, I.table) ::
    (List.range I.n).filterMap fun j =>
      if j = I.self then none
      else match rcv1.getD j none with
        | some m => (parseForward I ctx j m).map fun p => (j, p.2)
        | none => none
  (tables.flatMap fun jt => jt.2.filterMap fun e =>
    if e.1 ∈ S ∧ jt.1 ∈ S ∧ e.1 ≠ jt.1 ∧
        (match directRec I ctx b rcv0 e.1 with
          | some (k, _) => decide (e.2 ≠ k)
          | none => false) = true then
      some (min e.1 jt.1, max e.1 jt.1)
    else none).toFinset

/-- Output of `Π_Confirm` at `p` with input `b` (Protocol 1, step 2): `b` if
`|Supp_p| − ν(Γ_p) ≥ n − t` (compared without truncated subtraction), otherwise `⊥` (`none`). -/
def confirmResult (I : LocalInit) (ctx : Msg) (b : Bool) (rcv0 rcv1 : List (Option Msg)) :
    Option Bool :=
  if I.n + maxMatching (confirmConflicts I ctx b rcv0 rcv1) ≤
      (confirmSupp I ctx b rcv0 rcv1).card + I.t then some b else none

/-- The sends of one call of `Π_Confirm` whose first round is round `r0`. `step = 0`: send the
signed direct message to every party. `step = 1`: send every party the vector of valid direct
records received in round `r0` (own position: own message; invalid or missing: `nil`) together
with the own initial key table. -/
def confirmSend (I : LocalInit) (ctx : Msg) (b : Bool) (v : View) (r0 step : ℕ) :
    List (Option Expr) :=
  if step = 0 then List.replicate I.n (some (directExpr ctx I.self I.ownKey b))
  else
    let vecE := listExpr ((List.range I.n).map fun x =>
      if x = I.self then directExpr ctx I.self I.ownKey b
      else if (directRec I ctx b (v.getD r0 []) x).isSome then Expr.recv r0 x else Expr.nil)
    let tabE := listExpr (I.table.map fun e => Expr.cons (.num e.1) (.key e.2))
    List.replicate I.n (some (Expr.cons vecE tabE))

/-- **Protocol 1, `Π_Confirm`** as a standalone two-round protocol (call identifier `(0,0,0)`).
Input: `I.input`. Output after round 2: `some b` (its input) or `none` (`⊥`). -/
def PiConfirm : Protocol (Option Bool) where
  send I v :=
    let b := I.input.getD false
    if v.length < 2 then confirmSend I (callCtx I 0 0 0) b v 0 v.length else []
  decide I v :=
    if 2 ≤ v.length then
      some (confirmResult I (callCtx I 0 0 0) (I.input.getD false) (v.getD 0 []) (v.getD 1 []))
    else none

/-- First call of `Π_GBA` (Protocol 2, item 1) starting at round `r0` on bit `x`: returns the
updated candidate (`⊥ ↦ 0`) and grade (`1` iff the call returned `0`). -/
def gbaFirst (I : LocalInit) (proto phase : ℕ) (x : Bool) (v : View) (r0 : ℕ) : Bool × Bool :=
  let o := confirmResult I (callCtx I proto phase 0) x (v.getD r0 []) (v.getD (r0 + 1) [])
  (o.getD false, decide (o = some false))

/-- Result `(c_p, g_p)` of `Π_GBA` (Protocol 2): after the second call (rounds `r0+2, r0+3`) on
the updated candidate, set the grade to `1` if the call returned `1` (never resetting it), and
replace `⊥` by `1`. -/
def gbaResult (I : LocalInit) (proto phase : ℕ) (x : Bool) (v : View) (r0 : ℕ) : Bool × Bool :=
  let f := gbaFirst I proto phase x v r0
  let o := confirmResult I (callCtx I proto phase 1) f.1 (v.getD (r0 + 2) []) (v.getD (r0 + 3) [])
  (o.getD true, f.2 || decide (o = some true))

/-- The sends of `Π_GBA` in its round `s ∈ {0,1,2,3}` (both calls are always executed). -/
def gbaSend (I : LocalInit) (proto phase : ℕ) (x : Bool) (v : View) (r0 s : ℕ) :
    List (Option Expr) :=
  if s < 2 then confirmSend I (callCtx I proto phase 0) x v r0 s
  else if s < 4 then
    confirmSend I (callCtx I proto phase 1) (gbaFirst I proto phase x v r0).1 v (r0 + 2) (s - 2)
  else []

/-- **Protocol 2, `Π_GBA`** as a standalone four-round protocol (protocol tag `1`, phase `0`).
Output after round 4: `(c_p, g_p)` with `g_p = true` meaning grade `1`. -/
def PiGBA : Protocol (Bool × Bool) where
  send I v := if v.length < 4 then gbaSend I 1 0 (I.input.getD false) v 0 v.length else []
  decide I v := if 4 ≤ v.length then some (gbaResult I 1 0 (I.input.getD false) v 0) else none

/-- The bit received from the king: `1` for the message `1`, and `0` for `0`, for an invalid
message and for no message. -/
def kingBit : Option Msg → Bool
  | some (.num 1) => true
  | _ => false

/-- The current bit `x_p` of `Π_BA` at the start of phase `j` (phase `j` occupies rounds
`5j, …, 5j+4`; the king of phase `j` is party `j`). In the king round a party with grade `1` keeps
its candidate; otherwise it takes the king's bit (`0` if invalid or missing); the king uses its own
candidate. -/
def baBit (I : LocalInit) (v : View) : ℕ → Bool
  | 0 => I.input.getD false
  | j + 1 =>
      let cg := gbaResult I 2 j (baBit I v j) v (5 * j)
      if cg.2 then cg.1
      else if I.self = j then cg.1
      else kingBit ((v.getD (5 * j + 4) []).getD j none)

/-- **Protocol 3, `Π_BA`**: phases `j = 0, …, t`, each `Π_GBA` on the current bits (rounds
`5j … 5j+3`, protocol tag `2`) followed by a king round (round `5j+4`) in which king `j` sends its
candidate bit to every party. The kings `0, …, t` are `t + 1` distinct parties in a fixed public
order not depending on `G`. Output after round `5(t+1)`: the final current bit. -/
def PiBA : Protocol Bool where
  send I v :=
    if v.length < 5 * (I.t + 1) then
      let j := v.length / 5
      let s := v.length % 5
      let x := baBit I v j
      if s < 4 then gbaSend I 2 j x v (5 * j) s
      else if I.self = j then
        List.replicate I.n (some (Expr.num (bitNum (gbaResult I 2 j x v (5 * j)).1)))
      else []
    else []
  decide I v := if 5 * (I.t + 1) ≤ v.length then some (baBit I v (I.t + 1)) else none

end ShiAuthentication.BA


