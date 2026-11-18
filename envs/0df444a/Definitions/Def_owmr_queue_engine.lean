-- Prove2me | Definitions.Def_owmr_queue_engine
-- name    : owmr_queue_engine
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-16T00:53:54.444807+00:00
-- url     : https://prove2.me/theorems/45f48a21-4fe8-46a0-89dd-d8538953fe6c
-- title:
--   Warehouse request queue: FIFO allocation and threshold dispatch
-- statement:
--   This definition encodes the period-by-period mechanics shared by the FIFO policy (Definition 1) and the consolidation policy (Definition 2) once they have started. In each period $t$, after the scheduled receipts:
--
--   1. each retailer $i$ applies its $(s_i,S_i)$ rule to its inventory position including outstanding requests, $\widehat P_i=P_i+\Delta_i+R_i$, where $P_i$ is its net inventory plus stock in transit to it, $\Delta_i$ the unallocated quantity of its requests, and $R_i$ its **reserve**, the stock allocated to its requests but still held at the warehouse; if $\widehat P_i\le s_i$ it requests $S_i-\widehat P_i$, and positive requests join the end of one first-in, first-out queue, simultaneous requests in increasing retailer index;
--   2. the warehouse applies its $(s_0,S_0)$ rule to $W+O+\sum_i(P_i-c_i)$, where $W$ is warehouse stock, $O$ supplier stock in transit, and $c_i$ fixed centers; the order arrives $L_0$ periods later (at once if $L_0=0$), and each new request of a batch retailer receives an offset $\vartheta$ from an offset rule;
--   3. the unallocated warehouse stock is allocated to the requests in queue order, the last one possibly in part;
--   4. a request of a non-batch retailer ships each allocation at once, while a request of a batch retailer, of size $Q$, ships its whole reserve in a period in which its cumulative allocation rises to or past $3Q\vartheta/4$, rises to or past $3Q(1+\vartheta)/4$ when $\vartheta<1/3$, or reaches $Q$; all portions sent to one retailer in a period form one dispatch, which arrives $L_i$ periods later (at once if $L_i=0$);
--   5. demand occurs.
--
--   The state also defines the starting step: the policy may append **initial requests** of prescribed sizes before running these rules.
--
--   **Formalization Note** The state records the unallocated warehouse stock, the retailer net inventories, the scheduled arrivals by period, and the queue, where each request carries its retailer, size, cumulative allocation, shipped quantity, offset, and creation period. Initial requests are not ordinary requests; ordinary requests are indexed $j=1,2,\dots$ in creation order. $T_{\rm pipe}=\max(L_0,\max_iL_i)$; every prescribed pipeline quantity arrives by period $T_{\rm pipe}-1$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Definition 1 (ii)-(iii) (p. 8), Definition 2 (ii)-(iv) (p. 27), Section 5.1 (pp. 21-22), and Appendix C.2 (pp. E.10-E.12).

import Definitions.Def_owmr_single_location

/-!
# The warehouse request queue shared by the FIFO and consolidation policies

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems": Definition 1 (ii)–(iii) (FIFO policy), Definition 2 (ii)–(iv)
(consolidation policy), Section 5.1, and Appendix C.2.

Both policies run the same mechanism once started. In each period `t`, after the scheduled
receipts:
1. each retailer `i` applies its `(s_i, S_i)` rule to its inventory position including
   outstanding requests, `P̂_i = P_i + Δ_i + R_i` (`P_i`: net inventory plus stock in transit to
   `i`; `Δ_i`: unallocated quantity of its requests; `R_i`: reserve, i.e. stock allocated to its
   requests but still held at the warehouse); if `P̂_i ≤ s_i` it requests `S_i - P̂_i`, and a
   positive request joins the end of one FIFO queue (requests of one period in increasing
   retailer index);
2. the warehouse applies its `(s₀, S₀)` rule to `W + O + ∑_i (P_i - c_i)` (`W`: warehouse stock,
   `O`: supplier stock in transit, `c_i`: the retailer centers); an order arrives `L₀` periods
   later (at once if `L₀ = 0`);
3. the unallocated warehouse stock is allocated to the requests in queue order, the last one
   possibly in part;
4. a request of a non-batch retailer ships every allocation at once; a request of a batch
   retailer, of size `Q` and offset `ϑ`, ships its whole reserve in a period in which its
   cumulative allocation rises to or past a dispatch threshold (`3Qϑ/4`, and also
   `3Q(1+ϑ)/4` if `ϑ < 1/3`) or reaches `Q`; all portions sent to one retailer in a period form
   one dispatch, which arrives `L_i` periods later (at once if `L_i = 0`);
5. demand occurs.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

variable {n : ℕ}

/-- A retailer request in the warehouse queue. -/
structure Req (n : ℕ) where
  /-- requesting retailer -/
  ret : Fin n
  /-- request size `Q` -/
  size : ℝ
  /-- cumulative allocation -/
  alloc : ℝ
  /-- quantity shipped so far -/
  shipped : ℝ
  /-- offset `ϑ` (used only for requests of batch retailers) -/
  offset : ℝ
  /-- creation period -/
  born : ℕ

/-- State of a policy at the start of a period, before receipts. -/
structure EngState (n : ℕ) where
  /-- whether the policy has started (preparation finished) -/
  running : Bool
  /-- unallocated warehouse stock -/
  Wbar : ℝ
  /-- retailer net inventories -/
  I : Fin n → ℝ
  /-- scheduled supplier arrivals, by arrival period -/
  supPipe : ℕ → ℝ
  /-- scheduled arrivals at each retailer, by arrival period -/
  retPipe : Fin n → ℕ → ℝ
  /-- FIFO queue of requests (head first) -/
  queue : List (Req n)
  /-- number of ordinary requests created so far -/
  nOrd : ℕ

/-- Parameters of the queue mechanism: retailer rules `(s_i, S_i)`, centers `c_i` in the supplier
position, batch flags, and the supplier rule `(s₀, S₀)`. -/
structure EngParams (n : ℕ) where
  s : Fin n → ℝ
  S : Fin n → ℝ
  center : Fin n → ℝ
  batch : Fin n → Bool
  s0 : ℝ
  S0 : ℝ

/-- An offset rule: given the state at creation, the period, the ordinary-request index `j`
(starting at `1`), the retailer, and the request size, returns the offset `ϑ`. -/
abbrev OffsetRule (n : ℕ) := EngState n → ℕ → ℕ → Fin n → ℝ → ℝ

/-- The initial engine state for a prescribed initial state. -/
def initEngState (N : Network n) (x : InitState n) : EngState n where
  running := false
  Wbar := x.W
  I := x.I
  supPipe := fun t => if t < N.L0 then x.supPipe t else 0
  retPipe := fun i t => if t < N.L i then x.retPipe i t else 0
  queue := []
  nOrd := 0

/-- Scheduled receipts of period `t`. -/
def receive (st : EngState n) (t : ℕ) : EngState n :=
  { st with Wbar := st.Wbar + st.supPipe t, I := fun i => st.I i + st.retPipe i t }

/-- Demand of period `t`. -/
def applyDemand (st : EngState n) (dt : DemandVec n) : EngState n :=
  { st with I := fun i => st.I i - (dt i : ℝ) }

/-- Stock in transit to retailer `i` after the receipts of period `t`. -/
def inTransit (L : Fin n → ℕ) (st : EngState n) (t : ℕ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range (L i), st.retPipe i (t + 1 + k)

/-- Supplier stock in transit after the receipts of period `t`. -/
def supInTransit (L0 : ℕ) (st : EngState n) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range L0, st.supPipe (t + 1 + k)

/-- `Δ_i`: unallocated quantity of retailer `i`'s requests. -/
def unalloc (st : EngState n) (i : Fin n) : ℝ :=
  ((st.queue.filter (fun r => r.ret = i)).map (fun r => r.size - r.alloc)).sum

/-- `R_i`: reserve of retailer `i`'s requests (allocated, not yet shipped). -/
def reserve (st : EngState n) (i : Fin n) : ℝ :=
  ((st.queue.filter (fun r => r.ret = i)).map (fun r => r.alloc - r.shipped)).sum

/-- `P_i`: net inventory plus stock in transit to retailer `i`. -/
def physPos (L : Fin n → ℕ) (st : EngState n) (t : ℕ) (i : Fin n) : ℝ :=
  st.I i + inTransit L st t i

/-- `P̂_i = P_i + Δ_i + R_i`: inventory position including outstanding requests. -/
def phat (L : Fin n → ℕ) (st : EngState n) (t : ℕ) (i : Fin n) : ℝ :=
  physPos L st t i + unalloc st i + reserve st i

/-- Retailer `i`'s request in period `t` under its `(s_i, S_i)` rule. -/
def reqSize (L : Fin n → ℕ) (P : EngParams n) (st : EngState n) (t : ℕ) (i : Fin n) : ℝ :=
  if phat L st t i ≤ P.s i then P.S i - phat L st t i else 0

/-- Steps 1–2 of a running period (after receipts): retailer requests, the supplier order, and
the offsets of the new requests. Returns the state at creation (before allocation) and the
supplier order. -/
def phaseA (L0 : ℕ) (L : Fin n → ℕ) (P : EngParams n) (rule : OffsetRule n) (t : ℕ)
    (st : EngState n) : EngState n × ℝ :=
  let rs := (List.finRange n).filter (fun i => 0 < reqSize L P st t i)
  let pos := st.Wbar + ∑ i, reserve st i + supInTransit L0 st t
    + ∑ i, (physPos L st t i - P.center i)
  let q0 := if pos ≤ P.s0 then P.S0 - pos else 0
  let mk : Fin n → ℝ → Req n := fun i θ =>
    { ret := i, size := reqSize L P st t i, alloc := 0, shipped := 0, offset := θ, born := t }
  let st1 : EngState n :=
    { st with
      Wbar := if L0 = 0 then st.Wbar + q0 else st.Wbar
      supPipe := if L0 = 0 then st.supPipe
        else Function.update st.supPipe (t + L0) (st.supPipe (t + L0) + q0)
      queue := st.queue ++ rs.map (fun i => mk i 0)
      nOrd := st.nOrd + rs.length }
  let newReqs := rs.mapIdx (fun k i =>
    mk i (if P.batch i then rule st1 t (st.nOrd + k + 1) i (reqSize L P st t i) else 0))
  ({ st1 with queue := st.queue ++ newReqs }, q0)

/-- Whether the cumulative allocation of a batch request of size `Q` and offset `ϑ`, moving from
`prev` to `new` in one period, rises to or past a dispatch threshold (`3Qϑ/4`, and `3Q(1+ϑ)/4`
if `ϑ < 1/3`) or reaches `Q`. -/
abbrev crossesThreshold (Q θ prev new : ℝ) : Prop :=
  (prev < 3 * Q / 4 * θ ∧ 3 * Q / 4 * θ ≤ new) ∨
  (θ < 1 / 3 ∧ prev < 3 * Q / 4 * (1 + θ) ∧ 3 * Q / 4 * (1 + θ) ≤ new) ∨
  (prev < Q ∧ new = Q)

/-- FIFO allocation of the unallocated stock `w` and the resulting shipments; returns the updated
queue, the remaining unallocated stock, and the quantity shipped to each retailer. -/
def serve (batch : Fin n → Bool) : List (Req n) → ℝ → List (Req n) × ℝ × (Fin n → ℝ)
  | [], w => ([], w, 0)
  | r :: rs, w =>
    let a := min (r.size - r.alloc) w
    let r1 : Req n := { r with alloc := r.alloc + a }
    let ship : ℝ :=
      if batch r.ret = false ∨ crossesThreshold r.size r.offset r.alloc r1.alloc then
        r1.alloc - r1.shipped else 0
    let rest := serve batch rs (w - a)
    ({ r1 with shipped := r1.shipped + ship } :: rest.1, rest.2.1,
      rest.2.2 + Pi.single r.ret ship)

/-- Dispatch `q` in period `t`: arrives at once if `L_i = 0`, otherwise `L_i` periods later. -/
def sendOut (L : Fin n → ℕ) (t : ℕ) (q : Fin n → ℝ) (st : EngState n) : EngState n :=
  { st with
    I := fun i => if L i = 0 then st.I i + q i else st.I i
    retPipe := fun i => if L i = 0 then st.retPipe i
      else Function.update (st.retPipe i) (t + L i) (st.retPipe i (t + L i) + q i) }

/-- Steps 3–4 of a running period: allocation and dispatch. Fully shipped requests leave the
queue. Returns the new state and the dispatches. -/
def phaseB (L : Fin n → ℕ) (P : EngParams n) (t : ℕ) (st : EngState n) :
    EngState n × (Fin n → ℝ) :=
  let res := serve P.batch st.queue st.Wbar
  (sendOut L t res.2.2
    { st with Wbar := res.2.1, queue := res.1.filter (fun r => r.shipped < r.size) }, res.2.2)

/-- A running period after receipts: returns the state before demand, the supplier order, and
the dispatches. -/
def runStep (L0 : ℕ) (L : Fin n → ℕ) (P : EngParams n) (rule : OffsetRule n) (t : ℕ)
    (st : EngState n) : EngState n × ℝ × (Fin n → ℝ) :=
  let a := phaseA L0 L P rule t st
  let b := phaseB L P t a.1
  (b.1, a.2, b.2)

/-- Start the policy: append initial requests of the given sizes (the positive ones, in
increasing retailer index), with the given offsets; initial requests are not ordinary requests. -/
def startWith (st : EngState n) (t : ℕ) (sizes θ0 : Fin n → ℝ) : EngState n :=
  { st with
    running := true
    queue := st.queue ++ ((List.finRange n).filter (fun i => 0 < sizes i)).map (fun i =>
      { ret := i, size := sizes i, alloc := 0, shipped := 0, offset := θ0 i, born := t }) }

/-- The period by which every prescribed pipeline has arrived: `max(L₀, max_i L_i)`. -/
def Network.Tpipe (N : Network n) : ℕ := max N.L0 (Finset.univ.sup N.L)

end OWMR


