-- Prove2me | Definitions.Def_EulerianLE_chunkCode
-- name    : EulerianLE_chunkCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:36.625031+00:00
-- url     : https://prove2.me/theorems/a61ba5bb-df10-41dd-9326-9751a459a597
-- title:
--   Programs 2–6 and the four chunks Init, Counting, Check, Relay
-- statement:
--   The variables of a node are $\mathit{result}\in\{\emptyset,\text{Leader},\text{Non-Leader}\}$, its pairing $\pi$, and the variables of Programs 4–6. The module writes, in the language of `Code`:
--
--   1. **Program 2** (`SynchronizedCount`): for each port $i$ concurrently, $\mathtt{Send}(i,1)$, $\mathtt{BlockingRecv}(i,1)$, $\mathtt{Send}(i,1)$, $\mathtt{BlockingRecv}(i,1)$; join.
--   2. **Program 4** (`CheckIfLocalLeader`): probe the unclassified ports one at a time with two pulses, classify a port counting when the two pulses return to it and two ports non-counting with an arc $(i,j)$ of $W$ otherwise; orient the cycles of $\Gamma(\pi,W)$; merge them by splices; if some port is counting, rebalance with $\mathtt{Send}(i,2-\tilde\sigma_i)$ and $\mathtt{BlockingRecv}(i,2-\tilde\rho_i)$ and splice a remaining cycle with a pair outside it; succeed if no port is counting.
--   3. **Program 5** (`CheckIfGlobalLeader`): with $(\bar\imath_{CW},i_{CW})$ the lexicographically smallest stored pair, run concurrently the OR initiator on $(\bar\imath_{CW},i_{CW})$ and the OR participant with input $0$ on every other stored pair $(\bar\imath,i)$; succeed if every output is $0$.
--   4. **Program 6** (`SynchronizedRelay`): for each stored pair $(i,\bar\imath)$ concurrently, forward two pulses; classify the pair counting if one was consumed at each port, else non-counting with $i_{CW}$ the port that sent both; in the latter case wait for a pulse at $i$ or $\bar\imath$ and set $b=1$ exactly when it is at $\bar\imath_{CW}$ and some pair is unclassified or counting; run the OR participant $(b,\bar\imath_{CW},i_{CW})$; after the join, splice a witness pair with a counting pair; detect termination when every output is $0$.
--
--   The **chunks** (§5.1) are Init ($\pi\leftarrow$ the initial pairing $\{(2h-1,2h)\}$, $\mathit{result}\leftarrow\emptyset$), Counting (Program 2), Check (Programs 4 and 5; on success $\mathit{result}\leftarrow$ Leader and terminate) and Relay (Program 6; on termination $\mathit{result}\leftarrow$ Non-Leader and terminate). With $P^r_k$ = Init for $r=0$, Counting for $1\le r\le k$, Check for $r=k+1$ and Relay for $r>k+1$ (equation (1)), a chunk is a node program from $(\mathit{result},\pi)$ to $(\mathit{result},\pi)$; a `terminate` completes only the chunk.
--
--   **Formalization Note** Ports are 0-based. Every "arbitrary" choice picks the smallest port, Program 6's splice picks the first witness and counting pairs in stored order, and concurrent branches run in list order. The variables `probed` and `probeDone` record the probed ports and the end of the probing loop for Lemma 25; no program reads them.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §4.1, pp.19–21 (PDF pp.21–23), Programs 2–6; §5.1, p.23 (PDF p.25), chunks and equation (1)

import Mathlib
import Definitions.Def_EulerianLE_SameCircuit
import Definitions.Def_EulerianLE_Code

namespace EulerianLE

/-- The variable `result` of Program 1 (p.19): `∅`, `Leader` or `Non-Leader`. -/
inductive Result : Type
  | none
  | leader
  | nonLeader
  deriving DecidableEq, Repr

/-- The classification of a port (Program 4) or of a port pair (Program 6). -/
inductive PortClass : Type
  | unclassified
  | counting
  | nonCounting
  deriving DecidableEq, Repr

/-- The values `(result, π)` that a node passes from one chunk to the next (§5.1, p.23). -/
abbrev ChunkIO (deg : ℕ) : Type := Result × Pairs deg

/-- The variables of a node running Programs 1–8 (Frei, Gelles, Ghazy, Nolin, STOC 2027 submission
(manuscript sha256 90954a93…), §4.1, pp.19–22).

* `result`, `pi`: `result` and the port pairing `π` (Program 1).
* `W`, `pcls`: the arcs `W` and the port classifications of Program 4. `probed i` records that the
  probing loop has probed `i`, and `probeDone` that the loop has ended (both for the statement of
  Lemma 25; no program reads them). `cll`: the result of `CheckIfLocalLeader()` (`true` = success).
* `qcls`, `qout`: the classification of each port pair in Program 6 and the output `out` of each
  pair's OR instance in Programs 5 and 6, both recorded at the two ports of the pair. `cgl`: the
  result of `CheckIfGlobalLeader()`; `term`: `SynchronizedRelay()` detected termination. -/
structure Store (deg : ℕ) where
  result : Result
  pi : Pairs deg
  W : List (Fin deg × Fin deg)
  pcls : Fin deg → PortClass
  probed : Fin deg → Bool
  probeDone : Bool
  cll : Bool
  qcls : Fin deg → PortClass
  qout : Fin deg → Option OrOut
  cgl : Bool
  term : Bool

/-- Fresh variables with chunk input `x = (result, π)`: "All other variables start afresh in each
chunk" (§5.1, p.23). -/
def Store.fresh {deg : ℕ} (x : ChunkIO deg) : Store deg where
  result := x.1
  pi := x.2
  W := []
  pcls := fun _ => .unclassified
  probed := fun _ => false
  probeDone := false
  cll := false
  qcls := fun _ => .unclassified
  qout := fun _ => none
  cgl := false
  term := false

/-- A block of program text, as a function of the code that follows it. -/
abbrev Blk (deg : ℕ) : Type := Code deg (Store deg) → Code deg (Store deg)

variable {deg : ℕ}

/-- The initial pairing of Program 1, Line 1: `{(2h − 1, 2h) | h ∈ [deg(u)/2]}`, that is, the pairs
`(2h, 2h + 1)` of 0-based ports for `h < deg/2`. -/
def initPairs (deg : ℕ) : Pairs deg :=
  (List.range (deg / 2)).filterMap fun h =>
    if hh : 2 * h + 1 < deg then some (⟨2 * h, by omega⟩, ⟨2 * h + 1, hh⟩) else none

/-- `Send(i, n)`: `n` sends through `i`. -/
def sendN (i : Fin deg) : ℕ → Code deg (Store deg) → Code deg (Store deg)
  | 0, k => k
  | n + 1, k => .send i (sendN i n k)

/-- The statement `b` for every port, in increasing order. -/
def forPorts (b : Fin deg → Blk deg) : Blk deg := fun k => (List.finRange deg).foldr (fun i k' => b i k') k

/-- Program 2, `SynchronizedCount()` (p.19): reset the counters, then for each port `i` concurrently
`Send(i, 1)`, `BlockingRecv(i, 1)`, `Send(i, 1)`, `BlockingRecv(i, 1)`; join. -/
def countB : Blk deg := fun k =>
  .resetCounters <|
    .par ((List.finRange deg).map fun i => .send i (.recv i 1 (.send i (.recv i 1 .done)))) k

/-! ### The graph `Γ(π, W)` of Program 4 -/

/-- The traversal of `Γ(π, W)` from `p`, alternating matching edges and arcs, with fuel. -/
def cycleAux (π W : Pairs deg) (p : Fin deg) : ℕ → Fin deg → List (Fin deg) → Option (List (Fin deg))
  | 0, _, _ => none
  | n + 1, x, acc =>
    match otherEnd π x with
    | none => none
    | some y =>
      match otherEnd W y with
      | none => none
      | some z => if z = p then some (y :: x :: acc) else cycleAux π W p n z (y :: x :: acc)

/-- The vertices of the cycle of `Γ(π, W)` through `p`, if `p` lies on a cycle: Program 4, Line 12,
"Let Γ(π, W) have vertices [deg(u)], undirected matching edges π, and directed arcs W; cycles refer
to its underlying multigraph" (p.20). A pair that is both a matching edge and an arc is a 2-cycle. -/
def gammaCycle (π W : Pairs deg) (p : Fin deg) : Option (List (Fin deg)) := cycleAux π W p (deg + 1) p []

/-- The cycles of `Γ(π, W)`, each listed once (from its smallest vertex), ordered by smallest vertex. -/
def gammaCycles (π W : Pairs deg) : List (List (Fin deg)) :=
  (List.finRange deg).filterMap fun p =>
    (gammaCycle π W p).bind fun c => if c.all (fun q => decide (p ≤ q)) then some c else none

/-- Lexicographic order on ordered pairs of ports. -/
def lexLe (a b : Fin deg × Fin deg) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2))

/-- Program 4, Lines 14–16, on one cycle `cyc`: let `(i₁, i₂), (i₃, i₄), …, (i_{k−1}, i_k)` be the arcs of
the cycle in `W`, in lexicographic order; remove the pairs containing the `i_h` and add
`(i₂, i₃), (i₄, i₅), …, (i_k, i₁)`. -/
def orientCycle (π W : Pairs deg) (cyc : List (Fin deg)) : Pairs deg :=
  let arcs := (W.filter fun a => decide (a.1 ∈ cyc ∧ a.2 ∈ cyc)).mergeSort lexLe
  (π.filter fun a => decide (a.1 ∉ cyc ∧ a.2 ∉ cyc)) ++
    (arcs.zip (arcs.rotateLeft 1)).map fun ab => (ab.1.2, ab.2.1)

/-- The stored pair whose first component is the smallest port satisfying `P` that is a first
component (the refinement of "pick arbitrary", paper.md decision 6). -/
def firstPairWith (π : Pairs deg) (P : Fin deg → Bool) : Option (Fin deg × Fin deg) :=
  ((List.finRange deg).find? fun i => P i && π.any fun a => decide (a.1 = i)).bind fun i =>
    π.find? fun a => decide (a.1 = i)

/-- Some port is classified counting. -/
def anyCounting (s : Store deg) : Bool := (List.finRange deg).any fun i => decide (s.pcls i = .counting)

/-- Program 4, Lines 13–16, "for every cycle of Γ(π, W) at this point". -/
def orientAll (s : Store deg) : Store deg :=
  { s with pi := (gammaCycles s.pi s.W).foldl (fun π cyc => orientCycle π s.W cyc) s.pi }

/-- Program 4, Line 17: there are two disjoint cycles. -/
def twoCycles (s : Store deg) : Bool := decide (2 ≤ (gammaCycles s.pi s.W).length)

/-- Program 4, Lines 18–19: splice pairs `(i, ī)`, `(j, j̄)` with `i` on the first cycle and `j` on the
second. -/
def mergeStep (s : Store deg) : Store deg :=
  match gammaCycles s.pi s.W with
  | z₁ :: z₂ :: _ =>
    match firstPairWith s.pi (fun i => decide (i ∈ z₁)), firstPairWith s.pi (fun i => decide (i ∈ z₂)) with
    | some a, some b => { s with pi := splice s.pi a b }
    | _, _ => s
  | _ => s

/-- Program 4, Lines 23–25: if `Γ(π, W)` contains a cycle `Z`, splice pairs `(i, ī)`, `(j, j̄)` with
`i ∈ Z` and `j ∉ Z`. -/
def finalSplice (s : Store deg) : Store deg :=
  match gammaCycles s.pi s.W with
  | z :: _ =>
    match firstPairWith s.pi (fun i => decide (i ∈ z)), firstPairWith s.pi (fun i => decide (i ∉ z)) with
    | some a, some b => { s with pi := splice s.pi a b }
    | _, _ => s
  | [] => s

/-- The unclassified ports. -/
def unclassifiedSet (s : Store deg) : Finset (Fin deg) :=
  Finset.univ.filter fun i => s.pcls i = .unclassified

/-- The smallest unclassified port. -/
def firstUnclassified (s : Store deg) : Option (Fin deg) :=
  (List.finRange deg).find? fun i => decide (s.pcls i = .unclassified)

/-- One iteration of the probing loop, Program 4, Lines 4–11: probe the smallest unclassified port `i`
with `Send(i, 2)`; wait until at least two pulses are waiting at an unclassified port `j`;
`BlockingRecv(j, 2)`; classify `i` counting if `j = i`, else classify `i`, `j` non-counting and add the
arc `(i, j)` to `W`. -/
def probeIter : Code deg (Store deg) :=
  .get fun c =>
    match firstUnclassified c.store with
    | none => .done
    | some i =>
      .set (fun s => { s with probed := Function.update s.probed i true }) <|
      .send i <| .send i <|
      .waitAt 2 (unclassifiedSet c.store) fun j =>
      .recv j 2 <|
      if j = i then .set (fun s => { s with pcls := Function.update s.pcls i .counting }) .done
      else
        .set (fun s => { s with
          pcls := Function.update (Function.update s.pcls i .nonCounting) j .nonCounting
          W := s.W ++ [(i, j)] }) .done

/-- Program 4, Lines 21–22: `Send(i, 2 − σ̃_i)` for every port, then `BlockingRecv(i, 2 − ρ̃_i)` for every
port. -/
def rebalanceB : Blk deg := fun k =>
  forPorts (fun i k' => .get fun c => sendN i (2 - c.sig i) k') <|
  forPorts (fun i k' => .get fun c => .recv i (2 - c.rho i) k') k

/-- Program 4, `CheckIfLocalLeader()` (p.20). The result is stored in `cll`. -/
def cllB : Blk deg := fun k =>
  let setCll : Code deg (Store deg) := .set (fun s => { s with cll := !anyCounting s }) k
  .set (fun s => { s with W := [] }) <| .resetCounters <|
  .loop (fun c => (firstUnclassified c.store).isSome) probeIter <|
  .set (fun s => { s with probeDone := true }) <|
  .set orientAll <|
  .loop (fun c => twoCycles c.store) (.set mergeStep .done) <|
  .get fun c => if anyCounting c.store then rebalanceB (.set finalSplice setCll) else setCll

/-- Record the output `o` of the OR instance of the pair `a`. -/
def setOut (a : Fin deg × Fin deg) (o : OrOut) (s : Store deg) : Store deg :=
  { s with qout := Function.update (Function.update s.qout a.1 (some o)) a.2 (some o) }

/-- Classify the pair `a`. -/
def setQcls (a : Fin deg × Fin deg) (cl : PortClass) (s : Store deg) : Store deg :=
  { s with qcls := Function.update (Function.update s.qcls a.1 cl) a.2 cl }

/-- The lexicographically smallest stored pair. -/
def lexMin (π : Pairs deg) : Option (Fin deg × Fin deg) :=
  π.foldl (fun m a => match m with
    | none => some a
    | some b => if lexLe a b then some a else some b) none

/-- `out = 0` for all pairs. -/
def allZero (s : Store deg) : Bool := s.pi.all fun a => decide (s.qout a.1 = some .zero)

/-- Program 5, `CheckIfGlobalLeader()` (p.21): with `(ī_CW, i_CW)` the lexicographically smallest
pair, run concurrently for each stored pair `(ī, i)` the OR initiator `(ī, i)` if `i = i_CW` and the OR
participant `(b = 0, ī, i)` otherwise; join; succeed if every output is `0`. The result is stored
in `cgl`. -/
def cglB : Blk deg := fun k =>
  .get fun c =>
    let m := lexMin c.store.pi
    .par (c.store.pi.map fun a =>
        .orCall (if some a.2 = m.map (·.2) then .initiator else .participant false) a.1 a.2
          fun o => .set (setOut a o) .done)
      (.set (fun s => { s with cgl := allZero s }) k)

/-- The branch of the stored pair `a = (i, ī)` in Program 6, Lines 3–15: forward two pulses (each a
consumption at `i` or `ī` and a send through the other port of the pair); if `σ̃_i = σ̃_ī = 1`, classify
the pair counting, `i_CW ← i`, `b ← 0`; otherwise (`{σ̃_i, σ̃_ī} = {0, 2}`) classify it non-counting, let
`i_CW` be the port with `σ̃ = 2`, wait until a pulse is waiting at `i` or `ī`, selecting `i'`, and set
`b ← 1` if `i' = ī_CW` and some pair is unclassified or classified counting, else `b ← 0`; then run the
OR participant `(b, ī_CW, i_CW)`. -/
def relayBranch (a : Fin deg × Fin deg) : Code deg (Store deg) :=
  let other : Fin deg → Fin deg := fun s => if s = a.1 then a.2 else a.1
  let fwd : Code deg (Store deg) → Code deg (Store deg) := fun k =>
    .consumeAt {a.1, a.2} fun s => .send (other s) k
  let call : Bool → Fin deg → Fin deg → Code deg (Store deg) := fun b i j =>
    .orCall (.participant b) i j fun o => .set (setOut a o) .done
  fwd <| fwd <| .get fun c =>
    if c.sig a.1 = 1 ∧ c.sig a.2 = 1 then .set (setQcls a .counting) (call false a.2 a.1)
    else
      let icw := if c.sig a.1 = 2 then a.1 else a.2
      .set (setQcls a .nonCounting) <| .waitAt 1 {a.1, a.2} fun i' => .get fun c' =>
        call (decide (i' = other icw) &&
            c'.store.pi.any fun p => decide (c'.store.qcls p.1 ≠ .nonCounting))
          (other icw) icw

/-- Program 6, Lines 17–20, after the join: if some pair returned `(1, witness)` and some pair is
classified counting, splice the two (the first such pairs in stored order); record whether every
output is `0`. -/
def afterRelay (s : Store deg) : Store deg :=
  let s₁ :=
    match s.pi.find? (fun a => decide (s.qout a.1 = some (.one true))),
        s.pi.find? (fun a => decide (s.qcls a.1 = .counting)) with
    | some w, some cp => { s with pi := splice s.pi w cp }
    | _, _ => s
  { s₁ with term := allZero s }

/-- Program 6, `SynchronizedRelay()` (p.21): reset the counters; run `relayBranch` concurrently for each
stored pair; join; then `afterRelay`. The result is stored in `term`. -/
def relayB : Blk deg := fun k =>
  .resetCounters <| .get fun c => .par (c.store.pi.map relayBranch) (.set afterRelay k)

/-! ### Chunks (§5.1, p.23) -/

/-- The four chunks of Program 1: Init, Counting, Check and Relay. -/
inductive ChunkKind : Type
  | init
  | counting
  | check
  | relay
  deriving DecidableEq, Repr

/-- `P^r_k`, equation (1), p.23: Init if `r = 0`, Counting if `1 ≤ r ≤ k`, Check if `r = k + 1`, Relay if
`r > k + 1`. -/
def chunkKind (r k : ℕ) : ChunkKind :=
  if r = 0 then .init else if r ≤ k then .counting else if r = k + 1 then .check else .relay

/-- Start a chunk with fresh variables. -/
def freshB : Blk deg := fun k => .set (fun s => Store.fresh (s.result, s.pi)) k

/-- The Init chunk (Program 1, Lines 1–2): `π ←` the initial pairing, `result ← ∅`. -/
def initB : Blk deg := fun k => .set (fun _ => Store.fresh (.none, initPairs deg)) k

/-- The Counting chunk (Program 1, Line 4): Program 2. -/
def countingChunkB : Blk deg := fun k => freshB (countB k)

/-- The Check chunk (Program 1, Lines 5–8): if `CheckIfLocalLeader()` and then `CheckIfGlobalLeader()`
succeed, `result ← Leader` and `terminate`. -/
def checkChunkB : Blk deg := fun k =>
  freshB <| cllB <| .get fun c =>
    if c.store.cll then
      cglB (.get fun c' => if c'.store.cgl then .set (fun s => { s with result := .leader }) .halt else k)
    else k

/-- The Relay chunk (Program 1, Lines 10–12): if `SynchronizedRelay()` detects termination,
`result ← Non-Leader` and `terminate`. -/
def relayChunkB : Blk deg := fun k =>
  freshB <| relayB <| .get fun c =>
    if c.store.term then .set (fun s => { s with result := .nonLeader }) .halt else k

/-- The block of a chunk. -/
def chunkB : ChunkKind → Blk deg
  | .init => initB
  | .counting => countingChunkB
  | .check => checkChunkB
  | .relay => relayChunkB

/-- The program text of a chunk run on its own: the chunk, then completion. A `terminate` in the chunk
completes only the chunk (proof of Corollary 14, p.25). -/
def chunkCode (deg : ℕ) (kind : ChunkKind) : Code deg (Store deg) := chunkB kind .done

/-- A chunk as a node program on input `(result, π)`, with output `(result, π)` at completion
("Each chunk takes (result, π) as input and outputs their values at completion", p.23).

**Formalization Note.** Ports are 0-based (`Fin deg`); the paper's port `k` is `k − 1`. The paper's
"arbitrary" choices are refined to the smallest port, and concurrent branches to list order
(paper.md decision 6). -/
def chunkProg (deg : ℕ) (kind : ChunkKind) (x : ChunkIO deg) : NodeProg deg (ChunkIO deg) :=
  (chunkCode deg kind).prog (Store.fresh x) fun c => (c.store.result, c.store.pi)

end EulerianLE


