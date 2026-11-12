-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_CommitteeBroadcast
-- name    : SubcubicBA_PlainPKI_CommitteeBroadcast
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:44:05.423562+00:00
-- url     : https://prove2.me/theorems/1f587a16-531b-400c-bd04-f13efd83e65f
-- title:
--   CommitteeBroadcast: Dolev–Strong style broadcast with a committee
-- statement:
--   CommitteeBroadcast$(v_{in},p_{in},C)$ of §9.1 as a protocol of the execution model.
--
--   In round $0$ the sender $p_{in}\in C$ signs its value and sends the chain $(v,[(p_{in},\sigma)])$ to everyone. A chain is a value with a list of signatures; each signature is a member's signature on $(5,v)$ in the instance's session. For $i=2,\dots,|C|+1$, iteration $i$ consists of rounds $2i-3$ and $2i-2$:
--   1. In round $2i-3$ every party accepts the chains received that carry valid signatures of $p_{in}$ and of at least $i-1$ distinct members of $C$ ($p_{in}$ included), and forwards them to all members of $C$.
--   2. In round $2i-2$ every member of $C$ accepts such chains, adds its signature and sends them to everyone.
--
--   A party forwards and signs only for the first two distinct values it accepted; the order among simultaneous arrivals is an arbitrary key. After round $2|C|$ a party outputs $m$ if it accepted exactly the value $m$, and $\bot$ otherwise (`opt (some m)` resp. `opt none`).
--
--   This is the protocol of Lemma 10.
--
--   **Formalization Note** The source's "signed by $p_{in}$ and $i-1$ parties from $C$" is read as at least $i-1$ distinct members of $C$ including $p_{in}$, so that the sender's own chain is accepted at $i=2$.
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §9.1 CommitteeBroadcast (pp. 22–23)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # CommitteeBroadcast (§9.1, pp. 22–23)

`CommitteeBroadcast(v_in, p_in, C)`: the sender `p_in ∈ C` signs its value and sends it to all
parties (round `0`). Then for `i = 2, …, |C|+1`, iteration `i` lasts two rounds:
* in its first round (`2i-3`) every party, upon receiving a chain signed by `p_in` and `i-1`
  parties of `C` (here: `p_in` and at least `i-1` distinct members of `C` in total, `p_in`
  included), forwards it to all parties of `C`;
* in its second round (`2i-2`) every member of `C`, upon receiving such a chain, adds its
  signature and forwards it to all parties.
Both actions are applied only for the first two distinct values a party accepts. After the last
round (`2|C|`), a party returns `m` if it accepted exactly one value `m`, and `⊥` otherwise.

Encoding: a chain is `pair v sigs`, `sigs` a list of `pair (nat q) σ` with `σ` party `q`'s
signature on `pair (nat 5) v` in the instance's session; a message is a list of chains; the
output is `opt (some m)` or `opt none`. Acceptance thresholds: a chain received in round `x`
(sent in round `x-1`) is accepted if it carries valid signatures of `p_in` and of at least
`⌈x/2⌉` distinct members of `C` (this is `i-1` for both rounds `2i-3`, `2i-2` of iteration `i`);
in odd rounds every party accepts, in even rounds only members of `C` do. When several new values
or chains arrive in the same round, their order is the arbitrary order given by `ordKey`. -/

/-- Equality test. -/
def Obs.eqB (o : Obs) (a b : Expr) : Bool := o.test (.eq a b)

/-- Membership up to equality of values. -/
def Obs.memB (o : Obs) (a : Expr) (l : List Expr) : Bool := l.any (o.eqB a)

open Classical in
/-- Length of the list value of `e` (`0` if it is not a list). -/
noncomputable def Obs.listLen (o : Obs) (e : Expr) : ℕ :=
  if h : ∃ L, o.IsList e L then Nat.find h else 0

/-- The list expression of a list of expressions. -/
def listExpr : List Expr → Expr
  | [] => .nat 0
  | x :: xs => .pair x (listExpr xs)

/-- The content signed by a committee-broadcast signature on value `v`. -/
def cbData (v : Expr) : Expr := .pair (.nat 5) v

open Classical in
/-- The members of `C` with a valid signature (session `sess`) in the chain `c`. -/
noncomputable def cbSigners (o : Obs) (sess : ℕ) (C : Finset ℕ) (c : Expr) : Finset ℕ :=
  C.filter fun q => ∃ k < o.listLen (.snd c),
    o.shape ((Expr.snd c).nth k) = some (.pair (.nat q) .tok) ∧
    o.test (.isSig q sess (cbData (.fst c)) (.snd ((Expr.snd c).nth k))) = true

/-- Committee-broadcast state: accepted values (in order), values already forwarded, values
already signed. -/
structure CBState where
  acc : List Expr
  fwd : List Expr
  sgn : List Expr

open Classical in
/-- The chains received in round `x - 1` that are acceptable in round `x`, in the order given by
`ordKey self x sender position`. -/
noncomputable def cbCands (o : Obs) (I : LocalInit) (pin : ℕ) (C : Finset ℕ)
    (ordKey : ℕ → ℕ → ℕ → ℕ → ℕ) (x : ℕ) : List Expr :=
  let pos : List (ℕ × ℕ) := (List.range I.n).flatMap fun i =>
    (List.range (o.listLen (.recv (x - 1) i))).map fun k => (i, k)
  let ok : List (ℕ × ℕ) := pos.filter fun ik =>
    let c := (Expr.recv (x - 1) ik.1).nth ik.2
    decide (pin ∈ cbSigners o I.session C c ∧ (x + 1) / 2 ≤ (cbSigners o I.session C c).card)
  (ok.mergeSort fun a b => decide (ordKey I.self x a.1 a.2 ≤ ordKey I.self x b.1 b.2)).map
    fun ik => (Expr.recv (x - 1) ik.1).nth ik.2

/-- One round `x ≥ 1`: new state, chains to forward to `C`, chains to send to everybody. -/
noncomputable def cbStep (o : Obs) (I : LocalInit) (pin : ℕ) (C : Finset ℕ)
    (ordKey : ℕ → ℕ → ℕ → ℕ → ℕ) (x : ℕ) (st : CBState) : CBState × List Expr × List Expr :=
  let active : Bool := decide (x % 2 = 1 ∨ I.self ∈ C)
  let cs := if active then cbCands o I pin C ordKey x else []
  let acc' := cs.foldl (fun a c => if o.memB (.fst c) a then a else a ++ [.fst c]) st.acc
  let sel := acc'.take 2
  let chainFor (u : Expr) : Option Expr := cs.find? fun c => o.eqB (.fst c) u
  if x % 2 = 1 then
    let newF := sel.filterMap fun u =>
      if o.memB u st.fwd then none else (chainFor u).map fun c => (u, c)
    (⟨acc', st.fwd ++ newF.map Prod.fst, st.sgn⟩, newF.map Prod.snd, [])
  else
    let newS := sel.filterMap fun u =>
      if o.memB u st.sgn then none else (chainFor u).map fun c => (u, c)
    let signed := newS.map fun uc =>
      Expr.pair (.fst uc.2)
        (.pair (.pair (.nat I.self) (.signSelf [] (cbData (.fst uc.2)))) (.snd uc.2))
    (⟨acc', st.fwd, st.sgn ++ newS.map Prod.fst⟩, [], signed)

/-- State after processing rounds `1, …, x`. -/
noncomputable def cbStateAt (o : Obs) (I : LocalInit) (pin : ℕ) (C : Finset ℕ)
    (ordKey : ℕ → ℕ → ℕ → ℕ → ℕ) : ℕ → CBState
  | 0 => ⟨[], [], []⟩
  | x + 1 => (cbStep o I pin C ordKey (x + 1) (cbStateAt o I pin C ordKey x)).1

/-- CommitteeBroadcast with sender `pin`, committee `C` and arbitrary ordering `ordKey`. -/
noncomputable def committeeBroadcast (pin : ℕ) (C : Finset ℕ) (ordKey : ℕ → ℕ → ℕ → ℕ → ℕ) :
    Protocol where
  send I o j :=
    if o.round = 0 then
      (if I.self = pin then
        some (listExpr [.pair .input (listExpr [.pair (.nat pin) (.signSelf [] (cbData .input))])])
      else none)
    else if o.round ≤ 2 * C.card then
      let out := cbStep o I pin C ordKey o.round (cbStateAt o I pin C ordKey (o.round - 1))
      let chains := (if j ∈ C then out.2.1 else []) ++ out.2.2
      if chains = [] then none else some (listExpr chains)
    else none
  decide I o :=
    if o.round < 2 * C.card + 1 then none
    else
      match (cbStateAt o I pin C ordKey (2 * C.card + 1)).acc with
      | [v] => some (.pair (.nat 1) v)
      | _ => some (.nat 0)

end SubcubicBA.PlainPKI


