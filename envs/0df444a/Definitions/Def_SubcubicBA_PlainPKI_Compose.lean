-- Prove2me | Definitions.Def_SubcubicBA_PlainPKI_Compose
-- name    : SubcubicBA_PlainPKI_Compose
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:44:07.508411+00:00
-- url     : https://prove2.me/theorems/1d81e71b-d1a0-44f3-8277-fd632f5bb37f
-- title:
--   Composition of protocol instances; WeakBA, GradedAgreement and the recursive ByzantineAgreement
-- statement:
--   Composition operators of the execution model and the three compositional protocols.
--
--   **Sub-instances.** A sub-instance has a starting round, a contiguous group $[g,g+k)$ of parties, its own fault bound, the session `childSession s i` (so its signatures are tagged apart from every other instance, as in §13) and an input expression of the enclosing instance. A member runs the sub-protocol on the translated observation: only terms received from group members, rounds shifted by the start, indices renamed by $i\mapsto g+i$. Its outgoing expressions are translated back, and recipients outside the group are dropped. `subOut` reads the sub-instance's first decision made by a given number of its rounds. Sequential composition is round-by-round concatenation: a phase starts at the round bound of the previous one and reads its output there.
--
--   1. **WeakBA (p. 11).** Run proof creation (instance 0) for $T_1$ rounds, then validated dispersal (instance 1) for $T_2$ rounds on its output. Decide $v$ if the proofs output contain proofs for $v$ and none for $1-v$, else $\bot$.
--   2. **GradedAgreement (p. 41).** $v\leftarrow W(v_{in})$; $w\leftarrow1$ if $v\in\{1,\bot\}$ else $0$; $b\leftarrow W(w)$; return $(1,1)$ if $v=1$, $(1,0)$ if $b=1$, $(0,1)$ if $b=0$, and $(0,0)$ otherwise.
--   3. **ByzantineAgreement (pp. 40–41).** Below $M$ parties (or below 2) run a base protocol. Otherwise, with halves $P_1=[0,\lfloor n/2\rfloor)$ and $P_2$ the rest:
--      - $(v,g)\leftarrow GA_P(v_{in})$;
--      - the members of $P_1$ run $o\leftarrow BA_{P_1}(v)$ recursively, with fault bound $\lfloor(|P_1|-1)/2\rfloor$, and send $o$ to all;
--      - a party adopts $o$ if $g=0$ and a strict majority of $P_1$ sent $o$;
--      - the same steps follow with a second graded agreement and $P_2$;
--      - return $v$.
--
--      `baRounds` is its round bound $2T_{GA}(n)+T(\lfloor n/2\rfloor)+T(\lceil n/2\rceil)+2$.
--
--   These protocols state Theorems 3, 13 and 14.
--
--   **Formalization Note** The recursion needs $M\ge2$; below 2 parties the base protocol is used.
-- source:
--   Marc Dufay, Roger Wattenhofer, Optimal Subcubic Byzantine Agreement with Plain PKI, STOC 2027 submission #101 (October 2026), §6 WeakBA (p. 11); App. B.1 ByzantineAgreement (pp. 40–41); App. B.2 GradedAgreement (p. 41); §13 (pp. 36–37)

import Mathlib
import Definitions.Def_SubcubicBA_PlainPKI_Model
import Definitions.Def_SubcubicBA_PlainPKI_Proofs

set_option autoImplicit false

namespace SubcubicBA.PlainPKI

/-! # Composition of protocols in the execution model, and the compositional protocols
WeakBA (§6, p. 11), GradedAgreement (App. B.2, p. 41) and ByzantineAgreement (App. B.1,
pp. 40–41).

A sub-instance is embedded at a starting round, on a contiguous group `[g, g+k)` of parties,
with its own fault bound, with session `childSession s idx` (so its signatures are tagged apart
from every other instance, §13) and with an input expression of the enclosing instance. The
enclosing party runs the sub-protocol on the translated observation: received terms of the group
only, rounds shifted, sub-indices renamed; its outgoing expressions are translated back
(recipients outside the group are dropped). Sequential composition is round-by-round
concatenation: the next phase starts at the round bound of the previous one, and reads the
previous phase's first decision (made by that bound). -/

/-- Index renaming of a sub-instance on `[g, g+k)`: sub-index `i < k` is party `g + i`; the
remaining indices are mapped bijectively onto the remaining parties and non-parties. -/
def idxMap (g k i : ℕ) : ℕ := if i < k then g + i else if i - k < g then i - k else i

/-- An embedded sub-instance. -/
structure Embed where
  /-- first round of the sub-instance -/
  start : ℕ
  /-- group `[g, g + size)` -/
  g : ℕ
  size : ℕ
  /-- fault bound used by the sub-instance -/
  tSub : ℕ
  /-- sub-instance index: its session is `childSession s idx` -/
  idx : ℕ
  /-- its input, as an expression of the enclosing instance -/
  inp : Expr

/-- Translation of a sub-instance expression into the enclosing instance. -/
def Expr.lift (e : Embed) : Expr → Expr
  | .nat k => .nat k
  | .pair a b => .pair (Expr.lift e a) (Expr.lift e b)
  | .fst a => .fst (Expr.lift e a)
  | .snd a => .snd (Expr.lift e a)
  | .recv r i => if i < e.size then .recv (r + e.start) (e.g + i) else .bot
  | .input => e.inp
  | .hash a => .hash (Expr.lift e a)
  | .signSelf π a => .signSelf (e.idx :: π) (Expr.lift e a)
  | .bot => .bot

/-- Translation of a sub-instance test. -/
def Test.lift (e : Embed) : Test → Test
  | .eq a b => .eq (a.lift e) (b.lift e)
  | .isSig q s m σ => .isSig (idxMap e.g e.size q) s (m.lift e) (σ.lift e)

/-- The sub-instance's observation, read off the enclosing one. -/
def Obs.lift (o : Obs) (e : Embed) : Obs :=
  ⟨o.round - e.start, fun x => o.shape (x.lift e), fun τ => o.test (τ.lift e)⟩

/-- Forget the terms received in rounds `≥ r`. -/
def Expr.cut (r : ℕ) : Expr → Expr
  | .nat k => .nat k
  | .pair a b => .pair (Expr.cut r a) (Expr.cut r b)
  | .fst a => .fst (Expr.cut r a)
  | .snd a => .snd (Expr.cut r a)
  | .recv r' i => if r' < r then .recv r' i else .bot
  | .input => .input
  | .hash a => .hash (Expr.cut r a)
  | .signSelf π a => .signSelf π (Expr.cut r a)
  | .bot => .bot

def Test.cut (r : ℕ) : Test → Test
  | .eq a b => .eq (a.cut r) (b.cut r)
  | .isSig q s m σ => .isSig q s (m.cut r) (σ.cut r)

/-- The observation at the start of the earlier round `r`. -/
def Obs.cut (o : Obs) (r : ℕ) : Obs :=
  ⟨r, fun x => o.shape (x.cut r), fun τ => o.test (τ.cut r)⟩

/-- Public data of the sub-instance. -/
def LocalInit.sub (I : LocalInit) (e : Embed) : LocalInit :=
  ⟨childSession I.session e.idx, e.size, e.tSub, I.κ, I.self - e.g⟩

/-- `I.self` belongs to the group of `e`. -/
def Embed.Member (e : Embed) (I : LocalInit) : Prop := e.g ≤ I.self ∧ I.self < e.g + e.size

instance (e : Embed) (I : LocalInit) : Decidable (e.Member I) := by
  unfold Embed.Member; infer_instance

/-- What a group member sends to `j` as part of the sub-instance (round `≥ start`). -/
def subSend (P : Protocol) (e : Embed) (I : LocalInit) (o : Obs) (j : ℕ) : Option Expr :=
  if e.Member I ∧ e.g ≤ j ∧ j < e.g + e.size ∧ e.start ≤ o.round then
    (P.send (I.sub e) (o.lift e) (j - e.g)).map (Expr.lift e)
  else none

/-- The sub-instance's first decision among its rounds `0, …, L` (to be read at enclosing round
`≥ start + L`), translated into the enclosing instance. -/
def subOut (P : Protocol) (e : Embed) (I : LocalInit) (o : Obs) (L : ℕ) : Option Expr :=
  if e.Member I then
    ((List.range (L + 1)).findSome? fun r =>
      P.decide (I.sub e) ((o.cut (e.start + r)).lift e)).map (Expr.lift e)
  else none

/-! ## WeakBA (p. 11) -/

open Classical in
/-- WeakBA's decision on the dispersal output `S` (p. 11): `v` if the proofs in `S` are proofs
for the single value `v ∈ {0, 1}` (some element is a proof for `v` and none for `1 - v`), else
`⊥`. Proofs are checked with the signatures of session `sess`. -/
noncomputable def wbaDecision (o : Obs) (sess n t : ℕ) (S : Expr) : Expr :=
  let has (c : ℕ) : Prop := ∃ L k, o.IsList S L ∧ k < L ∧ o.ProofFor sess n t (S.nth k) c
  if has 0 ∧ ¬ has 1 then .nat 0 else if has 1 ∧ ¬ has 0 then .nat 1 else .nat 2

/-- WeakBA (p. 11): `proof ← ProofCreation(v_in)` (instance 0, rounds `[0, T₁)`), then
`proofs ← ValidatedDispersal(proof)` (instance 1, rounds `[T₁, T₁ + T₂)`), then decide. -/
noncomputable def weakBA (PC : Protocol) (T₁ : ℕ → ℕ → ℕ → ℕ) (VD : Protocol)
    (T₂ : ℕ → ℕ → ℕ → ℕ) : Protocol where
  send I o j :=
    let L₁ := T₁ I.n I.t I.κ
    let L₂ := T₂ I.n I.t I.κ
    let e₁ : Embed := ⟨0, 0, I.n, I.t, 0, .input⟩
    if o.round < L₁ then subSend PC e₁ I o j
    else if o.round < L₁ + L₂ then
      subSend VD ⟨L₁, 0, I.n, I.t, 1, (subOut PC e₁ I o L₁).getD (.nat 0)⟩ I o j
    else none
  decide I o :=
    let L₁ := T₁ I.n I.t I.κ
    let L₂ := T₂ I.n I.t I.κ
    let e₁ : Embed := ⟨0, 0, I.n, I.t, 0, .input⟩
    let e₂ : Embed := ⟨L₁, 0, I.n, I.t, 1, (subOut PC e₁ I o L₁).getD (.nat 0)⟩
    if o.round < L₁ + L₂ then none
    else some (wbaDecision o (childSession I.session 0) I.n I.t
      ((subOut VD e₂ I o L₂).getD (.nat 0)))

/-! ## GradedAgreement (p. 41) -/

/-- GradedAgreement from a weak agreement protocol `W` with round bound `T`: `v ← W(v_in)`
(instance 0), `w ← 1` if `v ∈ {1, ⊥}` else `0`, `b ← W(w)` (instance 1), then return `(1,1)` if
`v = 1`, `(1,0)` if `b = 1`, `(0,1)` if `b = 0`, `(0,0)` otherwise (as `pair (nat v) (nat g)`). -/
def gradedAgreement (W : Protocol) (T : ℕ → ℕ → ℕ → ℕ) : Protocol where
  send I o j :=
    let L := T I.n I.t I.κ
    let e₁ : Embed := ⟨0, 0, I.n, I.t, 0, .input⟩
    let v := (subOut W e₁ I o L).getD (.nat 2)
    let w : Expr :=
      if o.shape v = some (.nat 1) ∨ o.shape v = some (.nat 2) then .nat 1 else .nat 0
    if o.round < L then subSend W e₁ I o j
    else if o.round < 2 * L then subSend W ⟨L, 0, I.n, I.t, 1, w⟩ I o j
    else none
  decide I o :=
    let L := T I.n I.t I.κ
    let e₁ : Embed := ⟨0, 0, I.n, I.t, 0, .input⟩
    let v := (subOut W e₁ I o L).getD (.nat 2)
    let w : Expr :=
      if o.shape v = some (.nat 1) ∨ o.shape v = some (.nat 2) then .nat 1 else .nat 0
    let bb := (subOut W ⟨L, 0, I.n, I.t, 1, w⟩ I o L).getD (.nat 2)
    if o.round < 2 * L then none
    else if o.shape v = some (.nat 1) then some (.pair (.nat 1) (.nat 1))
    else if o.shape bb = some (.nat 1) then some (.pair (.nat 1) (.nat 0))
    else if o.shape bb = some (.nat 0) then some (.pair (.nat 0) (.nat 1))
    else some (.pair (.nat 0) (.nat 0))

/-! ## ByzantineAgreement (pp. 40–41) -/

/-- The fault bound used inside a group of `k` parties (the largest `t'` with `2t' < k`). -/
def tHalf (k : ℕ) : ℕ := (k - 1) / 2

/-- "`g = 0` and received the same `o` from a majority of the group `[g₀, g₀+k)` in round `ρ`":
then adopt `o`, else keep the graded-agreement value (first component of `ga`). -/
def adoptMajority (o : Obs) (ga : Expr) (g₀ k ρ : ℕ) : Expr :=
  let cnt (c : ℕ) : ℕ :=
    ((List.range k).filter fun q => decide (o.shape (.recv ρ (g₀ + q)) = some (.nat c))).length
  let grade0 : Bool :=
    match o.shape ga with
    | some (.pair (.nat _) (.nat 0)) => true
    | _ => false
  if grade0 = true ∧ k < 2 * cnt 0 then .nat 0
  else if grade0 = true ∧ k < 2 * cnt 1 then .nat 1
  else .fst ga

/-- Round bound of ByzantineAgreement: `T_base` below `M` (or below `2`), otherwise
`2 T_GA(n) + T(⌊n/2⌋) + T(⌈n/2⌉) + 2`. -/
def baRounds (TGA Tb : ℕ → ℕ → ℕ → ℕ) (M : ℕ) (n t κ : ℕ) : ℕ :=
  if h : n < M ∨ n < 2 then Tb n t κ
  else
    have h1 : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    have h2 : n - n / 2 < n := by
      have : 0 < n / 2 := Nat.div_pos (by omega) (by norm_num)
      omega
    2 * TGA n t κ + baRounds TGA Tb M (n / 2) (tHalf (n / 2)) κ +
      baRounds TGA Tb M (n - n / 2) (tHalf (n - n / 2)) κ + 2
termination_by n

/-- One recursion level of ByzantineAgreement for `n` parties, given the protocols `B₁`, `B₂`
used on the halves `P₁ = [0, ⌊n/2⌋)` and `P₂ = [⌊n/2⌋, n)` and their round bounds `L₁ κ`, `L₂ κ`:
`(v,g) ← GA_P(v_in)`; `P₁` runs `o ← B₁(v)` and sends `o` to all; adopt `o` if `g = 0` and a
majority of `P₁` sent `o`; `(v,g) ← GA_P(v)`; `P₂` runs `o ← B₂(v)` and sends `o`; adopt as
before; return `v`. Sub-instances 1, 2, 3, 4 are GA, `B₁`, GA, `B₂`. -/
def baLevel (GA : Protocol) (TGA : ℕ → ℕ → ℕ → ℕ) (B₁ B₂ : Protocol) (L₁ L₂ : ℕ → ℕ) :
    Protocol where
  send I o j :=
    let n₁ := I.n / 2
    let n₂ := I.n - I.n / 2
    let LA := TGA I.n I.t I.κ
    let eA : Embed := ⟨0, 0, I.n, I.t, 1, .input⟩
    let outA := (subOut GA eA I o LA).getD (.pair (.nat 0) (.nat 0))
    let eB : Embed := ⟨LA, 0, n₁, tHalf n₁, 2, .fst outA⟩
    let cC := LA + L₁ I.κ
    let v₁ := adoptMajority o outA 0 n₁ cC
    let cD := cC + 1
    let eD : Embed := ⟨cD, 0, I.n, I.t, 3, v₁⟩
    let outD := (subOut GA eD I o LA).getD (.pair (.nat 0) (.nat 0))
    let eE : Embed := ⟨cD + LA, n₁, n₂, tHalf n₂, 4, .fst outD⟩
    let cF := cD + LA + L₂ I.κ
    if o.round < LA then subSend GA eA I o j
    else if o.round < cC then subSend B₁ eB I o j
    else if o.round = cC then (if I.self < n₁ then subOut B₁ eB I o (L₁ I.κ) else none)
    else if o.round < cD + LA then subSend GA eD I o j
    else if o.round < cF then subSend B₂ eE I o j
    else if o.round = cF then (if n₁ ≤ I.self then subOut B₂ eE I o (L₂ I.κ) else none)
    else none
  decide I o :=
    let n₁ := I.n / 2
    let n₂ := I.n - I.n / 2
    let LA := TGA I.n I.t I.κ
    let eA : Embed := ⟨0, 0, I.n, I.t, 1, .input⟩
    let outA := (subOut GA eA I o LA).getD (.pair (.nat 0) (.nat 0))
    let cC := LA + L₁ I.κ
    let v₁ := adoptMajority o outA 0 n₁ cC
    let cD := cC + 1
    let eD : Embed := ⟨cD, 0, I.n, I.t, 3, v₁⟩
    let outD := (subOut GA eD I o LA).getD (.pair (.nat 0) (.nat 0))
    let cF := cD + LA + L₂ I.κ
    if o.round < cF + 1 then none else some (adoptMajority o outD n₁ n₂ cF)

/-- ByzantineAgreement for exactly `n` parties: the base protocol below `M` (or below `2`),
otherwise one recursion level over the protocols for `⌊n/2⌋` and `⌈n/2⌉` parties. -/
def baAt (GA : Protocol) (TGA : ℕ → ℕ → ℕ → ℕ) (Base : Protocol) (Tb : ℕ → ℕ → ℕ → ℕ)
    (M : ℕ) (n : ℕ) : Protocol :=
  if h : n < M ∨ n < 2 then Base
  else
    have h1 : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
    have h2 : n - n / 2 < n := by
      have : 0 < n / 2 := Nat.div_pos (by omega) (by norm_num)
      omega
    baLevel GA TGA (baAt GA TGA Base Tb M (n / 2)) (baAt GA TGA Base Tb M (n - n / 2))
      (fun κ => baRounds TGA Tb M (n / 2) (tHalf (n / 2)) κ)
      (fun κ => baRounds TGA Tb M (n - n / 2) (tHalf (n - n / 2)) κ)
termination_by n

/-- ByzantineAgreement (pp. 40–41) as one protocol family: a party with `n` parties in its
instance runs `baAt … n`. -/
def byzantineAgreement (GA : Protocol) (TGA : ℕ → ℕ → ℕ → ℕ) (Base : Protocol)
    (Tb : ℕ → ℕ → ℕ → ℕ) (M : ℕ) : Protocol where
  send I := (baAt GA TGA Base Tb M I.n).send I
  decide I := (baAt GA TGA Base Tb M I.n).decide I

end SubcubicBA.PlainPKI


