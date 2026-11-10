-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm
-- name    : IncrOpenAddr_NoTradeoff_Algorithm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:36:26.0032+00:00
-- url     : https://prove2.me/theorems/7eb554b8-ab3d-47c9-a255-c2e000271555
-- title:
--   TryInsertSubtree, the insertion algorithms of §2, §3 and §4, and the record of each insertion
-- statement:
--   The table is an array of $n$ cells, each empty or holding one key. A node is **full** if all its slots are occupied. A node **encodes the bit** $1$ if its first two slots hold two keys in decreasing order, and $0$ otherwise (a root uses its first two slots).
--
--   **TryInsertSubtree$(x,i,j)$ (Algorithm 1).** Let $V$ be the level-$j$ ancestor of $L_i(x)$ in $T_i$. If $V$ is full, fail. Otherwise descend from $U=V$: while $U$ is not a leaf and some child of $U$ is nonfull, move to the child above $L_i(x)$ if there is one and it is nonfull, else to a nonfull child; place $x$ in an empty slot of $U$.
--
--   **§2 insertion** of $u$ in epoch $i$, phase $j$: (1) *cleanup attempt*: in the final phase of an epoch $i\ge2$, TryInsertSubtree$(u,i-1,h)$ with $h$ the height of $T_{i-1}$; in a nonfinal phase $j$ with $g_{i-1}(u)<1/j^4$, TryInsertSubtree$(u,i-1,j)$; (2) otherwise or on failure, *current-array insertion*: TryInsertSubtree$(u,i,\ell)$ for $\ell=1,2,\dots$ until one succeeds (the algorithm fails if none does).
--
--   **§3 insertion** of $x$ in epoch $s$: if $s\le2$ insert $x$ by §2; otherwise put $x$ in place of the element $y$ in the first slot of $L_1(x)$ ($y$ is **evicted**) and insert $y$ by §2.
--
--   **§4 insertion** of $x$ in epoch $s$: step 1 as in §3; step 2 (*leave a trail*): with $u$ the element placed by §2 in tree $T_i$ and $j$ the smallest level such that $u$ lies in its level-$j$ home subtree, unless $u$ lies in its own level-$j$ ancestor and $g_i(u)<1/j^4$, set to $1$ the bits of $u$'s ancestors at levels $1,\dots,j-1$; step 3 (*record the eviction*), for $s>100$: with $\ell=\lceil s/100\rceil$, $V$ the level-$\ell$ ancestor of $L_1(x)$ and $w$ the other element of $L_1(x)$, if $V$ holds an element $v$ with $g_1(v)<1/\ell^4$, exchange $v$ and $w$ and, if $V$ is an ancestor of $L_1(v)$, set to $1$ the bit of the child of $V$ above $L_1(v)$; otherwise set to $1$ the bits of $L_1(x)$ and its ancestors below $V$. Every node the insertion touches keeps its bit except those deliberately set.
--
--   Inserting a key list $xs$ in order from the empty table (`runAll`) yields the table after the first $t$ insertions (`tableAt`) and one **record** per insertion (`recs`): its epoch and phase, the element placed by §2, the target of the cleanup attempt and whether it succeeded, the targets of the current-array calls, the node where the element was placed, the evicted element, the node selected by step 3, whether a step tried to set the bit of a nonfull node, and the **cost**: the number of node reads and writes of the §2 algorithm plus one for reading the priority.
--
--   **Formalization Note.** Choices the paper leaves free are fixed so that every touched node keeps its bit: the first empty slot of $U$, then the node's first two slots sorted increasingly if $x$ landed there; the left child when $U$ is off $x$'s path; §3/§4 step 1 reorders the leaf's two keys to keep its bit; step 3 takes the first slot of $V$ with a candidate $v$ and reorders both nodes after the exchange; setting a bit puts the first two keys in decreasing order. An attempt to set the bit of a nonfull node does nothing and is recorded.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 8–9 (PDF 9–10), Algorithm 1 and §2.1.1; p. 17 (PDF 18), §3; p. 19–20 (PDF 20–21), §4 steps 1–3 and footnote 4

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel

set_option autoImplicit false

/-!
# The construction: TryInsertSubtree, the insertion algorithms of §2, §3 and §4, and their trace

Farach-Colton, Krapivin, Kuszmaul, arXiv:2611.04186 (manuscript sha256 9486c2b8…):
Algorithm 1 and §2.1.1 (p. 8–9, PDF 9–10); §3 (p. 17, PDF 18); §4, node bits and insertion
steps 1–3 (p. 19–20, PDF 20–21).

The table is an array `ℕ → Option K` (only addresses `< n` are ever used).  The construction is
run on the idealized hashes of `Def_IncrOpenAddr_NoTradeoff_HashModel`; every insertion records
what it did (`Rec`), which is what the analysis talks about.

Implementation choices the paper leaves free (each preserves every node's bit, as §4 requires):
* `TryInsertSubtree` places its element in the first empty slot of the final node `U`; if that
  slot is one of the node's first two slots, the first two slots are then put in increasing order
  (the node held at most one element there, so its bit was `0` and stays `0`).
* When the preferred child is full or `U` is off the element's path, the descent takes the
  nonfull child (the left one if both are nonfull and `U` is off the path).
* §3 step 1 writes `x` into the first slot of `L₁(x)`; in the §4 algorithm the two first slots
  of that leaf are then reordered to keep its bit (BRIEF pitfall: "reordering the leaf's two keys").
* §4 step 3 takes the first slot of `V` holding an element `v` with `g₁(v) < 1/ℓ⁴`; after the
  exchange both nodes are reordered to keep their bits, then the bit is set as the paper says.
* Setting a bit to `1` puts the node's first two elements in decreasing order; an attempt to set
  the bit of a nonfull node does nothing and is recorded (`badBit`), see Lemma 4.1.
Cost (`cost`) counts node reads and writes: one per node `TryInsertSubtree` inspects or writes,
plus one for reading the priority.
-/

namespace IncrOpenAddr.NoTradeoff

variable {K : Type} [LinearOrder K]

/-- The table: array address ↦ content. -/
abbrev Arr (K : Type) := ℕ → Option K

/-- The empty table. -/
def emptyArr : Arr K := fun _ => none

/-- The elements stored in node `v`, in slot order. -/
def nodeElems (n : ℕ) (A : Arr K) (v : Node) : List K := (slots n v).filterMap A

/-- Node `v` is full: every slot it covers is occupied. -/
def nodeFull (n : ℕ) (A : Arr K) (v : Node) : Bool := (slots n v).all fun a => (A a).isSome

/-- The bit a node encodes (§4 and footnote 4): `1` iff its first two slots hold two elements in
decreasing order. -/
def nodeBit (n : ℕ) (A : Arr K) (v : Node) : Bool :=
  match slots n v with
  | a :: b :: _ => match A a, A b with
    | some x, some y => decide (y < x)
    | _, _ => false
  | _ => false

/-- Reorder the contents of addresses `a`, `b` (if both occupied) so that they encode `bit`. -/
def arrangeTwo (A : Arr K) (a b : ℕ) (bit : Bool) : Arr K :=
  match A a, A b with
  | some x, some y =>
      if decide (y < x) = bit then A else Function.update (Function.update A a (some y)) b (some x)
  | _, _ => A

/-- Reorder the first two slots of node `v` so that it encodes `bit` (when they are full). -/
def arrangeBit (n : ℕ) (A : Arr K) (v : Node) (bit : Bool) : Arr K :=
  match slots n v with
  | a :: b :: _ => arrangeTwo A a b bit
  | _ => A

/-- Place `x` in node `v` (`Algorithm 1`, line 7), keeping the node's bit `0`. -/
def placeIn (n : ℕ) (A : Arr K) (v : Node) (x : K) : Arr K :=
  match (slots n v).find? (fun a => (A a).isNone) with
  | none => A
  | some a =>
      let A' := Function.update A a (some x)
      if a ∈ (slots n v).take 2 then arrangeBit n A' v false else A'

/-- The descent of `Algorithm 1`, lines 4–6, from node `U` for an element with home leaf `ℓ`:
while `U` is not a leaf and some child of `U` is nonfull, move to the child above `ℓ` if there is
one and it is nonfull, else to a nonfull child.  Returns the final node and the number of node
reads. -/
def descend (n ℓ : ℕ) (A : Arr K) : ℕ → Node → Node × ℕ
  | 0, U => (U, 0)
  | fuel + 1, U =>
      if U.level ≤ 1 then (U, 0) else
        let c0 : Node := ⟨U.tree, U.level - 1, 2 * U.idx⟩
        let c1 : Node := ⟨U.tree, U.level - 1, 2 * U.idx + 1⟩
        let pref : Node :=
          if U.idx = ℓ / 2 ^ (U.level - 1) then ancestor U.tree ℓ (U.level - 1) else c0
        let other : Node := if pref = c0 then c1 else c0
        if !nodeFull n A pref then
          let r := descend n ℓ A fuel pref
          (r.1, r.2 + 2)
        else if !nodeFull n A other then
          let r := descend n ℓ A fuel other
          (r.1, r.2 + 2)
        else (U, 2)

/-- The outcome of a call of `TryInsertSubtree`. -/
structure TryRes (K : Type) where
  ok : Bool
  arr : Arr K
  /-- the target node (the level-`j` ancestor) -/
  target : Node
  /-- the node where the element was placed (the target if the call failed) -/
  node : Node
  cost : ℕ

/-- `TryInsertSubtree(x, i, j)` (Algorithm 1) for an element `x` with home leaf `ℓ = L_i(x)`. -/
def tryInsert (n : ℕ) (A : Arr K) (x : K) (i ℓ j : ℕ) : TryRes K :=
  let V := ancestor i ℓ j
  if nodeFull n A V then ⟨false, A, V, V, 1⟩
  else
    let r := descend n ℓ A j V
    ⟨true, placeIn n A r.1 x, V, r.1, r.2 + 2⟩

/-- The current-array insertion: `TryInsertSubtree(x, i, j)` for `j, j + 1, …` (at most `fuel`
calls) until one succeeds.  Returns the targets of the calls made, the resulting table and node
(`none` if every call failed) and the cost. -/
def caLoop (n : ℕ) (A : Arr K) (x : K) (i ℓ : ℕ) : ℕ → ℕ → List Node × Option (Arr K × Node) × ℕ
  | 0, _ => ([], none, 0)
  | fuel + 1, j =>
      let r := tryInsert n A x i ℓ j
      if r.ok then ([r.target], some (r.arr, r.node), r.cost)
      else
        let rest := caLoop n A x i ℓ fuel (j + 1)
        (r.target :: rest.1, rest.2.1, r.cost + rest.2.2)

/-- What the algorithm of §2 did when inserting one element. -/
structure Sec2Res (K : Type) where
  arr : Arr K
  /-- the target of the cleanup attempt, if one was made -/
  cleanupTarget : Option Node
  cleanupOK : Bool
  /-- the targets of the calls of the current-array insertion (empty if none was made) -/
  caTargets : List Node
  /-- where the element was placed (`none`: the algorithm failed) -/
  placed : Option Node
  cost : ℕ

/-- The insertion algorithm of §2 (p. 9, PDF 10), inserting element `u` when `c` elements are
present: 1. the cleanup attempt (epoch `i ≥ 2`: in the final phase `TryInsertSubtree(u, i-1, h)`
with `h` the height of `T_{i-1}`; in a nonfinal phase `j` with `g_{i-1}(u) < 1/j⁴`,
`TryInsertSubtree(u, i-1, j)`); 2. otherwise or on failure, the current-array insertion into
`T_i`. -/
noncomputable def sec2Insert (n : ℕ) (η : ℝ) {K : Type} [LinearOrder K] (ω : Outcome K n) (c : ℕ)
    (A : Arr K) (u : K) : Sec2Res K :=
  let i := epochOf n η c
  let ph := phaseOf n η c
  let h := height n (i - 1)
  let call : Option ℕ :=
    if i ≤ 1 then none
    else if ph = h + 1 then some h
    else if prio ω u (i - 1) < 1 / (ph : ℝ) ^ 4 then some ph else none
  let ca := fun (B : Arr K) => caLoop n B u i (leafOf ω u i) (height n i) 1
  match call with
  | some j =>
      let r := tryInsert n A u (i - 1) (leafOf ω u (i - 1)) j
      if r.ok then ⟨r.arr, some r.target, true, [], some r.node, 1 + r.cost⟩
      else
        let q := ca A
        ⟨(q.2.1.map Prod.fst).getD A, some r.target, false, q.1, q.2.1.map Prod.snd,
          1 + r.cost + q.2.2⟩
  | none =>
      let q := ca A
      ⟨(q.2.1.map Prod.fst).getD A, none, false, q.1, q.2.1.map Prod.snd, 1 + q.2.2⟩

/-- Set the bit of node `v` to `1`; the flag records an attempt on a nonfull node (which then
does nothing). -/
def setBitOne (n : ℕ) (A : Arr K) (v : Node) : Arr K × Bool :=
  if nodeFull n A v then (arrangeBit n A v true, false) else (A, true)

/-- Set to `1` the bits of the ancestors at the given levels of leaf `ℓ` of tree `i`. -/
def setBitsAnc (n : ℕ) (A : Arr K) (i ℓ : ℕ) (levels : List ℕ) : Arr K × Bool :=
  levels.foldl (fun (acc : Arr K × Bool) j =>
    let r := setBitOne n acc.1 (ancestor i ℓ j)
    (r.1, acc.2 || r.2)) (A, false)

/-- §4 step 3, "record the eviction", for the insertion of `x` with `ℓ = ⌈s/100⌉`: let `V` be the
level-`ℓ` ancestor of `L₁(x)` and `w` the element of `L₁(x)` other than `x`; if `V` holds an
element `v` with `g₁(v) < 1/ℓ⁴`, exchange `v` and `w` and, if `V` is an ancestor of `L₁(v)`, set
the bit of the child of `V` above `L₁(v)`; otherwise set the bits of `L₁(x)` and of its ancestors
below `V`. -/
noncomputable def step3 (n : ℕ) {K : Type} [LinearOrder K] (ω : Outcome K n) (A : Arr K) (x : K)
    (ℓ : ℕ) : Arr K × Bool :=
  let leaf := leafOf ω x 1
  let L := ancestor 1 leaf 1
  let V := ancestor 1 leaf ℓ
  let isCand : ℕ → Bool := fun a => match A a with
    | some v => decide (prio ω v 1 < 1 / (ℓ : ℝ) ^ 4)
    | none => false
  match (slots n V).find? isCand, (slots n L).find? (fun a => A a ≠ some x ∧ (A a).isSome) with
  | some av, some aw =>
      match A av, A aw with
      | some v, some w =>
          let B := Function.update (Function.update A av (some w)) aw (some v)
          let B := arrangeBit n (arrangeBit n B V (nodeBit n A V)) L (nodeBit n A L)
          if leafOf ω v 1 / 2 ^ (ℓ - 1) = V.idx then setBitOne n B (ancestor 1 (leafOf ω v 1) (ℓ - 1))
          else (B, false)
      | _, _ => (A, false)
  | _, _ => setBitsAnc n A 1 leaf ((List.range (ℓ - 1)).map (· + 1))

/-- Which insertion algorithm: §2 (no reordering), §3 (eviction), §4 (eviction and
breadcrumbs). -/
inductive Variant where
  | sec2 | sec3 | sec4
  deriving DecidableEq, Repr

/-- The record of one insertion. -/
structure Rec (K : Type) where
  /-- the inserted key -/
  key : K
  epoch : ℕ
  /-- the phase (`0` in epoch one; `h + 1` is the final phase) -/
  phase : ℕ
  /-- the element the algorithm of §2 placed (`key`, or the evicted element) -/
  placedKey : K
  /-- what the algorithm of §2 did with it -/
  s2 : Sec2Res K
  /-- the element evicted from `L₁(key)` (§3), if any -/
  evicted : Option K
  /-- the node `V` selected by §4 step 3, if any -/
  step3Node : Option Node
  /-- some step tried to set the bit of a nonfull node -/
  badBit : Bool
  cost : ℕ

/-- One insertion of key `x` when `c` elements are present, by the algorithm of the given
section. -/
noncomputable def insertOne (var : Variant) (n : ℕ) (η : ℝ) {K : Type} [LinearOrder K]
    (ω : Outcome K n) (c : ℕ) (A : Arr K) (x : K) : Arr K × Rec K :=
  let s := epochOf n η c
  let ph := phaseOf n η c
  let L := ancestor 1 (leafOf ω x 1) 1
  let s0 := (slots n L).headD 0
  -- step 1 (§3): put `x` in place of the element `y` in the first slot of `L₁(x)`, insert `y`
  let st1 : Arr K × K × Option K :=
    if var = .sec2 ∨ s ≤ 2 then (A, x, none)
    else match A s0 with
      | none => (A, x, none)
      | some y =>
          let A' := Function.update A s0 (some x)
          ((if var = .sec4 then arrangeBit n A' L (nodeBit n A L) else A'), y, some y)
  let u := st1.2.1
  let r := sec2Insert n η ω c st1.1 u
  -- step 2 (§4): leave a trail
  let st2 : Arr K × Bool :=
    if var = .sec4 then
      match r.placed with
      | none => (r.arr, false)
      | some U =>
          let i := U.tree
          let ℓ := leafOf ω u i
          let j := homeLevel n ℓ U
          if j = U.level ∧ prio ω u i < 1 / (j : ℝ) ^ 4 then (r.arr, false)
          else setBitsAnc n r.arr i ℓ ((List.range (j - 1)).map (· + 1))
    else (r.arr, false)
  -- step 3 (§4): record the eviction
  let ℓ3 := (s + 99) / 100
  let doStep3 : Bool := var = .sec4 ∧ 100 < s ∧ ℓ3 ≤ height n 1
  let st3 : Arr K × Bool := if doStep3 then step3 n ω st2.1 x ℓ3 else (st2.1, false)
  (st3.1, ⟨x, s, ph, u, r, st1.2.2, (if doStep3 then some (ancestor 1 (leafOf ω x 1) ℓ3) else none),
    st2.2 || st3.2, r.cost + (if var = .sec2 then 0 else 1)⟩)

/-- Insert the keys `xs` in order into the empty table: the final table and the records. -/
noncomputable def runAll (var : Variant) (n : ℕ) (η : ℝ) {K : Type} [LinearOrder K]
    (ω : Outcome K n) (xs : List K) : Arr K × List (Rec K) :=
  xs.foldl (fun (st : Arr K × List (Rec K)) x =>
    let r := insertOne var n η ω st.2.length st.1 x
    (r.1, st.2 ++ [r.2])) (emptyArr, [])

/-- The table after the first `t` insertions. -/
noncomputable def tableAt (var : Variant) (n : ℕ) (η : ℝ) {K : Type} [LinearOrder K]
    (ω : Outcome K n) (xs : List K) (t : ℕ) : Arr K :=
  (runAll var n η ω (xs.take t)).1

/-- The records of all insertions of `xs`, in order. -/
noncomputable def recs (var : Variant) (n : ℕ) (η : ℝ) {K : Type} [LinearOrder K]
    (ω : Outcome K n) (xs : List K) : List (Rec K) :=
  (runAll var n η ω xs).2

end IncrOpenAddr.NoTradeoff


