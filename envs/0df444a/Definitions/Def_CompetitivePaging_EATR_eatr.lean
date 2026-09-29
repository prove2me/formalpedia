-- Prove2me | Definitions.Def_CompetitivePaging_EATR_eatr
-- name    : CompetitivePaging_EATR_eatr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:14:21.998875+00:00
-- url     : https://prove2.me/theorems/3b7f53dc-8ac9-4637-b546-03c7bdb186eb
-- title:
--   Algorithm EATR for the uniform 2-server problem, its phases, and its expected cost
-- statement:
--   This file defines algorithm EATR ("end after twice requested") of Fiat, Karp, Luby, McGeoch, Sleator and Young, a randomized on-line algorithm for the uniform $2$-server problem (paging with a cache of two pages), together with the phase structure it induces and the quantities used in its analysis.
--
--   **Bookkeeping.** The algorithm starts with its two servers on two given vertices $a$ and $b$ (the paper's vertices $1$ and $2$). It keeps a deterministic record consisting of
--   1. $P$, the set of vertices occupied by its servers at the end of the previous phase (initially $\{a,b\}$);
--   2. whether a phase is in progress;
--   3. $\ell$, the most recently requested vertex;
--   4. $R$, the set of vertices requested during the current phase (empty between phases).
--
--   A vertex $v$ is **clean** if $v\notin P\cup R$: it was not occupied by a server at the end of the previous phase and has not been requested during this phase. A vertex is **stale** if it is not clean and is not the most recently requested vertex; the stale set is
--   $$\mathrm{Stale}=(P\cup R)\setminus\{\ell\}.$$
--
--   **The algorithm.** Between phases the servers occupy $P$. A request to a vertex of $P$ moves nothing; a request to a vertex $r\notin P$ starts a phase: the server that stays is chosen uniformly at random from $P$ and the other one moves to $r$. During a phase one server is on $\ell$ and the other, at vertex $X$, is uniformly distributed on the stale set. On a request to $r$:
--   1. if $r=\ell$, nothing moves;
--   2. if $r$ is clean, a vertex $y$ is drawn uniformly from $\mathrm{Stale}\cup\{\ell\}$; if $y=\ell$ the server at $X$ moves to $r$ (and the stationary server is now the one on $\ell$), otherwise the server on $\ell$ moves to $r$; then $\ell:=r$ and $r$ joins $R$;
--   3. if $r$ is stale, the servers are placed on the two most recently requested vertices $\ell$ and $r$ (the server at $X$ moves to $r$ unless it is already there), the phase ends, and $P:=\{\ell,r\}$.
--
--   The **expected cost** $C_{\mathrm{EATR}}(\sigma)$ on a request sequence $\sigma$ is the expected total number of server moves; each move costs $1$ in the uniform metric. The file also defines, for a request sequence $\sigma$, when request $t$ starts or ends a phase, when the indices $i,\dots,i'-1$ form a **complete phase**, the number $l$ of clean vertices requested in it, the expected EATR cost of those requests, the cost $C_A$ of a deterministic algorithm $A$ on them, the number of servers of $A$ that do not coincide with EATR's servers at a given time (the paper's $d$ and $d'$), and **lazy** algorithms (no move on a covered request, exactly one server moved to the request otherwise).
--
--   These are the objects about which Theorem 3 and its proof speak; every other item of the mission is stated in terms of them.
--
--   **Formalization Note** The paper prescribes only the marginal law of the second server during a phase (uniform on the stale set) and does not say how it is moved when the stale set grows after a clean request. The two-point coupling in rule 2 is a modelling choice: it moves exactly one server, and it keeps $X$ uniform on the enlarged stale set. The expected cost is computed as $\sum_t \mathbb E[\,|\text{servers}_{t+1}\setminus\text{servers}_t|\,]$, the expected number of newly covered vertices per request, which equals the number of server moves. The branch "no phase in progress, request outside $P$, $P=\emptyset$" is unreachable and is given only to make the step total. The model reuses the published `KServer` definitions (configurations, move cost, deterministic on-line algorithms).
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 6, §4 (Algorithm EATR); p. 4, §3 (lazy algorithms, d and d′); p. 1 (expected cost)

import Mathlib
import Definitions.Def_KServer_model

open scoped ENNReal

namespace CompetitivePaging.EATR

/-- The deterministic bookkeeping of algorithm EATR (it does not depend on the random choices).
* `prev`: the vertices occupied by EATR's servers at the end of the previous phase (initially
  the two starting vertices);
* `inPhase`: whether a phase is in progress;
* `last`: the most recently requested vertex (meaningful while a phase is in progress);
* `req`: the set of vertices requested so far during the current phase (empty between phases). -/
structure Book (M : Type*) where
  prev : Finset M
  inPhase : Bool
  last : M
  req : Finset M

/-- The initial bookkeeping: EATR's servers are on the vertices `a` and `b`, no phase is in
progress, and no vertex has been requested. (`last := b` is a placeholder: `last` is only read
while a phase is in progress, and every phase starts by setting it.) -/
def initBook {M : Type*} [DecidableEq M] (a b : M) : Book M :=
  ⟨{a, b}, false, b, ∅⟩

/-- A vertex is **clean** if it was not occupied by a server at the end of the previous phase
and has not been requested during this phase. -/
def IsClean {M : Type*} [DecidableEq M] (B : Book M) (v : M) : Prop :=
  v ∉ B.prev ∪ B.req

/-- The set of **stale** vertices: those that are not clean and are not the most recently
requested vertex, i.e. `(prev ∪ req) \ {last}`. -/
def stale {M : Type*} [DecidableEq M] (B : Book M) : Finset M :=
  (B.prev ∪ B.req).erase B.last

/-- The deterministic bookkeeping update on a request to `r`.
* Between phases: a request to a vertex of `prev` (a covered vertex) changes nothing; a request
  to any other vertex starts a phase, with `last := r` and `req := {r}`.
* During a phase: a request to `last` changes nothing; a request to a clean vertex `r` sets
  `last := r` and adds `r` to `req`; a request to a stale vertex `r` ends the phase, the servers
  being placed on the two most recently requested vertices, `prev := {last, r}`. -/
def bookStep {M : Type*} [DecidableEq M] (B : Book M) (r : M) : Book M :=
  if B.inPhase then
    if r = B.last then B
    else if r ∉ B.prev ∪ B.req then ⟨B.prev, true, r, insert r B.req⟩
    else ⟨{B.last, r}, false, r, ∅⟩
  else
    if r ∈ B.prev then B
    else ⟨B.prev, true, r, {r}⟩

/-- The bookkeeping after serving the request list `l`, starting from `initBook a b`. -/
def bookAfter {M : Type*} [DecidableEq M] (a b : M) (l : List M) : Book M :=
  l.foldl bookStep (initBook a b)

/-- The full (random) state of EATR: the bookkeeping `book` and the position `other` of the
server that is not on the most recently requested vertex. -/
structure State (M : Type*) where
  book : Book M
  other : M

/-- The set of vertices covered by EATR's two servers in state `s`: between phases the servers
are on `prev`; during a phase one server is on `last` and the other on `other`. -/
def servers {M : Type*} [DecidableEq M] (s : State M) : Finset M :=
  if s.book.inPhase then {s.book.last, s.other} else s.book.prev

/-- One step of algorithm EATR on a request to `r`, as a probability distribution over the next
state.
* Between phases, a request to a vertex of `prev` moves nothing. A request to `r ∉ prev` starts a
  phase: the server that stays (the new `other`) is chosen uniformly at random from `prev`, and
  the other server moves to `r`.
* During a phase, a request to `last` moves nothing. A request to a clean vertex `r`: a vertex `y`
  is drawn uniformly from the new stale set `stale ∪ {last}`; if `y = last` the server on `other`
  moves to `r` (so the new `other` is the old `last`), otherwise the server on `last` moves to `r`
  (so `other` is unchanged). This coupling is a modelling choice: the paper prescribes only that
  `other` is uniform on the stale set, and this is a lazy way to keep it so.
* During a phase, a request to a stale vertex `r`: the servers are placed on `last` and `r` (the
  server on `other` moves to `r` unless it is already there), and the phase ends.
The branch `prev = ∅` is never reached from `initBook a b`; it is given only to make the
definition total. -/
noncomputable def step {M : Type*} [DecidableEq M] (s : State M) (r : M) : PMF (State M) :=
  let B := s.book
  if B.inPhase then
    if r = B.last then PMF.pure s
    else if r ∉ B.prev ∪ B.req then
      (PMF.uniformOfFinset (insert B.last (stale B)) (Finset.insert_nonempty _ _)).map
        (fun y => ⟨bookStep B r, if y = B.last then B.last else s.other⟩)
    else PMF.pure ⟨bookStep B r, B.last⟩
  else
    if r ∈ B.prev then PMF.pure s
    else if h : B.prev.Nonempty then
      (PMF.uniformOfFinset B.prev h).map (fun x => ⟨bookStep B r, x⟩)
    else PMF.pure ⟨bookStep B r, s.other⟩

/-- The initial state of EATR: servers on `a` and `b`. -/
def initState {M : Type*} [DecidableEq M] (a b : M) : State M :=
  ⟨initBook a b, a⟩

/-- The law of EATR's state after serving the request list `l`, starting from `initState a b`. -/
noncomputable def lawAfter {M : Type*} [DecidableEq M] (a b : M) (l : List M) : PMF (State M) :=
  l.foldl (fun p r => p.bind (fun s => step s r)) (PMF.pure (initState a b))

/-- The expected number of servers EATR moves when, in state `s`, it serves a request to `r`:
the expectation, over the next state `s'`, of the number of vertices covered in `s'` but not in
`s` (each server move costs `1` in the uniform metric). -/
noncomputable def stepMoves {M : Type*} [DecidableEq M] (s : State M) (r : M) : ℝ≥0∞ :=
  ∑' s' : State M, step s r s' * ((servers s' \ servers s).card : ℝ≥0∞)

/-- The expected cost of EATR (started on `a`, `b`) on the request with index `t` of `σ`
(and `0` if `t` is out of range). -/
noncomputable def eatrStepCost {M : Type*} [DecidableEq M] (a b : M) (σ : List M) (t : ℕ) : ℝ :=
  if h : t < σ.length then
    (∑' s : State M, lawAfter a b (σ.take t) s * stepMoves s (σ.get ⟨t, h⟩)).toReal
  else 0

/-- The expected cost `C_EATR(σ)` of algorithm EATR, started with its servers on `a` and `b`, on
the request sequence `σ`: the expected total number of server moves. -/
noncomputable def eatrExpCost {M : Type*} [DecidableEq M] (a b : M) (σ : List M) : ℝ :=
  ∑ t ∈ Finset.range σ.length, eatrStepCost a b σ t

/-- The expected cost of EATR on the requests with indices `i, i+1, …, i'-1` of `σ`. -/
noncomputable def eatrPhaseCost {M : Type*} [DecidableEq M] (a b : M) (σ : List M)
    (i i' : ℕ) : ℝ :=
  ∑ t ∈ Finset.Ico i i', eatrStepCost a b σ t

/-- Request `t` of `σ` starts a phase: no phase is in progress and `σ(t)` is not covered
(it is not in `prev`). -/
def IsPhaseStart {M : Type*} [DecidableEq M] (a b : M) (σ : List M) (t : ℕ) : Prop :=
  ∃ h : t < σ.length, (bookAfter a b (σ.take t)).inPhase = false ∧
    σ.get ⟨t, h⟩ ∉ (bookAfter a b (σ.take t)).prev

/-- Request `t` of `σ` ends a phase: a phase is in progress and `σ(t)` is a stale vertex. -/
def IsPhaseEnd {M : Type*} [DecidableEq M] (a b : M) (σ : List M) (t : ℕ) : Prop :=
  ∃ h : t < σ.length, (bookAfter a b (σ.take t)).inPhase = true ∧
    σ.get ⟨t, h⟩ ∈ stale (bookAfter a b (σ.take t))

/-- The requests with indices `i, …, i'-1` of `σ` form a complete EATR phase: request `i` starts
a phase, request `i' - 1` ends it, and no request strictly in between ends a phase. -/
def IsCompletePhase {M : Type*} [DecidableEq M] (a b : M) (σ : List M) (i i' : ℕ) : Prop :=
  i < i' ∧ IsPhaseStart a b σ i ∧ IsPhaseEnd a b σ (i' - 1) ∧
    ∀ u, i ≤ u → u < i' - 1 → ¬ IsPhaseEnd a b σ u

/-- Request `t` of `σ` is a request to a clean vertex. -/
def IsCleanRequest {M : Type*} [DecidableEq M] (a b : M) (σ : List M) (t : ℕ) : Prop :=
  ∃ h : t < σ.length, IsClean (bookAfter a b (σ.take t)) (σ.get ⟨t, h⟩)

open Classical in
/-- `l`: the number of requests to clean vertices among the requests with indices
`i, …, i'-1` of `σ` (in a phase, the number of clean vertices requested during it). -/
noncomputable def numClean {M : Type*} [DecidableEq M] (a b : M) (σ : List M) (i i' : ℕ) : ℕ :=
  ((Finset.Ico i i').filter (fun t => IsCleanRequest a b σ t)).card

/-- A deterministic on-line algorithm for two (or `k`) servers is **lazy**: it moves no server
in response to a request to a covered vertex, and otherwise it moves exactly one server, to the
requested vertex. -/
def IsLazy {k : ℕ} {M : Type*} [MetricSpace M] (A : KServer.OnlineAlgorithm k M) : Prop :=
  (∀ (l : List M) (r : M), (∃ i, A.conf l i = r) → A.conf (l ++ [r]) = A.conf l) ∧
    (∀ (l : List M) (r : M), ∃ i : Fin k, A.conf (l ++ [r]) = Function.update (A.conf l) i r)

/-- The cost incurred by the algorithm `A` on the requests with indices `i, …, i'-1` of `σ`. -/
noncomputable def algPhaseCost {k : ℕ} {M : Type*} [MetricSpace M]
    (A : KServer.OnlineAlgorithm k M) (σ : List M) (i i' : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico i i', KServer.moveCost (A.conf (σ.take j)) (A.conf (σ.take (j + 1)))

open Classical in
/-- The number of servers of `A` that do not coincide with any of EATR's servers just before
request `t` of `σ` (EATR's servers are then on `prev` whenever no phase is in progress, in
particular at the beginning and at the end of every phase). With `t` the first request of a
phase this is the paper's `d`; with `t` one past the last request of a phase it is `d′`. -/
noncomputable def mismatch {k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M] (a b : M)
    (A : KServer.OnlineAlgorithm k M) (σ : List M) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => A.conf (σ.take t) i ∉ (bookAfter a b (σ.take t)).prev)).card

end CompetitivePaging.EATR


